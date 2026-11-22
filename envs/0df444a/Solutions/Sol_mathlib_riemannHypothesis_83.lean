-- Prove2me | solution 83 for mathlib_riemannHypothesis
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T22:36:39.843934+00:00
-- url     : https://prove2.me/submissions/f7c65235-4bc0-4923-bd1d-4891d2cba286
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_MasulloRH_RegularizedTrace
import Theorems.Thm_MasulloRH_narrow_window_resolvent_cutoff_inequality_at_three
import Theorems.Thm_MasulloRH_regularized_arch_limit
import Theorems.Thm_MasulloRH_regularized_initial_identity_full_strip
import Theorems.Thm_MasulloRH_regularized_mellin_limit
import Theorems.Thm_MasulloRH_regularized_prime_limit
import Theorems.Thm_MasulloRH_regularized_spectral_limit
import Theorems.Thm_MasulloRH_single_resolvent_test
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Definitions.Def_MasulloRH_RationalTrace
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
import Mathlib.Analysis.Complex.RealDeriv
import Theorems.Thm_MasulloRH_even_test_omitted_sum_eq_four_mul_upper_right
import Mathlib.Analysis.Calculus.Taylor
import Mathlib.Analysis.Normed.Group.Tannery
import Mathlib.NumberTheory.LSeries.ZetaZeros
import Mathlib.Topology.Algebra.Module.Cardinality
import Mathlib.Topology.Compactness.Lindelof
import Theorems.Thm_MasulloAudit_trace_formula_rational_of_half_le
import Theorems.Thm_MasulloAudit_trace_formula_window_with_remainder
import Theorems.Thm_MasulloAudit_geometric_side_eq_formal_lhs
import Theorems.Thm_MasulloRH_trace_formula_inversion_odd
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Tactic.LinearCombination
import Mathlib.NumberTheory.Padics.ProperSpace
import Mathlib.MeasureTheory.Measure.Haar.Basic
import Mathlib.Analysis.Calculus.ContDiff.RCLike
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Theorems.Thm_MasulloRH_trace_formula_rational_iff_RH

-- Step 1: `MasulloRH.narrow_window_resolvent_cutoff_inequality_at_three` implies `MasulloRH.even_real_upper_right_omitted_sum_zero_for_interval_positive_test` (accepted reduction of `MasulloRH.even_real_upper_right_omitted_sum_zero_for_interval_positive_test`).
section

set_option autoImplicit false

open MasulloRH MeasureTheory Set Filter
open scoped Topology

-- The polar limit calculation follows the full-strip proof by davidloeffler
-- and the accepted endpoint adaptation df176fb8-4037-4112-be76-52bbcbea3294.
private theorem realPolarLimit :
    Tendsto (fun n : ℕ => cutoffPolar n (3 : ℂ)) atTop
      (𝓝 (regularizedPolar (3 : ℂ))) := by
  have hplus := regularized_mellin_limit (3 : ℂ) (1 / 2) (by norm_num) (by norm_num)
  have hminus := regularized_mellin_limit (3 : ℂ) (-1 / 2) (by norm_num) (by norm_num)
  convert hplus.add hminus using 1 <;>
    simp only [cutoffPolar, regularizedPolar] <;> congr 2 <;> ring

theorem MasulloRH.even_real_upper_right_omitted_sum_zero_for_interval_positive_test
    (α : ℝ) (hα : 0 < α) (hα2 : α < 1 / 2)
    (ψ : ℝ → ℝ) (hψ : IsRationalTraceTest (fun t => (ψ t : ℂ)))
    (heven : ∀ t : ℝ, 0 < t → ψ t⁻¹ = ψ t)
    (hNonneg : ∀ t : ℝ, 0 ≤ ψ t)
    (r : ℝ) (hr : 0 < r) (hr1 : r < 1)
    (hStrict : ∀ t : ℝ, 0 < ψ t ↔ t ≠ 1 ∧ (t - 1) ^ 2 / (1 + t ^ 2) < r)
    (hBoundary : ∀ z : ℂ, riemannZeta z = 0 → z.re = 1 / 2 + α → 0 < z.im → False) :
    ∑' ρ : {ρ : ℂ // riemannZeta ρ = 0 ∧ 1 / 2 + α ≤ ρ.re ∧ ρ.re < 1 ∧ 0 < ρ.im},
      (analyticOrderNatAt riemannZeta (ρ : ℂ) : ℝ) *
        (mellin (fun t => (ψ t : ℂ)) ((ρ : ℂ) - 1 / 2)).re = 0 := by
  have hThree : (3 / 2 : ℝ) < (3 : ℂ).re := by norm_num
  have hGeom := (regularized_arch_limit (3 : ℂ) hThree).add
    (regularized_prime_limit (3 : ℂ) hThree)
  have hSpec := realPolarLimit.sub (regularized_spectral_limit α hα hα2 (3 : ℂ) hThree)
  have hLimit :
      Tendsto (fun n : ℕ =>
        (cutoffArch n 3 + cutoffPrime n 3 - (cutoffPolar n 3 - cutoffSpectral α n 3)).re)
        atTop (𝓝 ((regularizedArch 3 + (-zetaLogDeriv 3 + zetaLogDeriv (5 / 2)) -
          (regularizedPolar 3 - regularizedSpectral α 3)).re)) :=
    (Complex.continuous_re.tendsto _).comp (hGeom.sub hSpec)
  have hPositive := ge_of_tendsto_of_frequently hLimit
    ((narrow_window_resolvent_cutoff_inequality_at_three α hα hα2 hBoundary).mono
      (fun n hn => sub_nonneg.mpr hn))
  have hScalar : (regularizedTraceRHS (1 / 2) 3).re ≤ (regularizedTraceRHS α 3).re := by
    rw [regularized_initial_identity_full_strip (3 : ℂ) hThree]
    simp only [regularizedTraceRHS, Complex.add_re, Complex.sub_re, Complex.neg_re] at hPositive ⊢
    linarith only [hPositive]
  have hWindow := (single_resolvent_test α).mp hScalar
  let Z := {ρ : ℂ // riemannZeta ρ = 0 ∧ 1 / 2 + α ≤ ρ.re ∧ ρ.re < 1 ∧ 0 < ρ.im}
  have : IsEmpty Z := ⟨fun z => by
    have hz0 : 0 < (z : ℂ).re := by linarith [z.property.2.1]
    have hz1 : (z : ℂ).re < 1 := z.property.2.2.1
    have hzwin : |(z : ℂ).re - 1 / 2| < 1 / 2 :=
      abs_lt.mpr ⟨by linarith, by linarith⟩
    have hz := (abs_lt.mp (hWindow ⟨z.val, z.property.1, hz0, hz1, hzwin⟩)).2
    linarith [z.property.2.1]⟩
  change ∑' ρ : Z, _ = 0
  exact tsum_empty

end

-- Step 2: `MasulloRH.even_real_upper_right_omitted_sum_zero_for_interval_positive_test` implies `MasulloRH.even_real_upper_right_omitted_sum_zero_of_no_boundary_zero_nonneg` (accepted reduction of `MasulloRH.even_real_upper_right_omitted_sum_zero_of_no_boundary_zero_nonneg`).
section

open MasulloRH MeasureTheory Set Filter Metric
open scoped Topology ContDiff
set_option autoImplicit false

private theorem intervalTest (ψ : ℝ → ℝ)
    (hψ : IsRationalTraceTest (fun t => (ψ t : ℂ))) :
    ∃ (g : ℝ → ℝ) (r : ℝ), 0 < r ∧ r < 1 ∧
      IsRationalTraceTest (fun t => (g t : ℂ)) ∧
      (∀ t : ℝ, 0 < t → g t⁻¹ = g t) ∧
      (∀ t : ℝ, 0 ≤ g t) ∧
      (∀ t : ℝ, 0 < g t ↔ t ≠ 1 ∧ (t - 1) ^ 2 / (1 + t ^ 2) < r) ∧
      (∀ t ∈ tsupport (fun t => (ψ t : ℂ)), (t - 1) ^ 2 / (1 + t ^ 2) < r) := by
  have hSupport : tsupport (fun t => (ψ t : ℂ)) = tsupport ψ :=
    tsupport_comp_eq (g := Complex.ofReal) (by simp) ψ
  have hCompact : HasCompactSupport ψ := by
    change IsCompact (tsupport ψ)
    rw [← hSupport]
    exact hψ.2.1.isCompact
  have hPosSupp : tsupport ψ ⊆ Ioi 0 := by
    rw [← hSupport]
    exact hψ.2.2.1
  -- This smooth coordinate is inversion-invariant on the positive reals.
  let u (t : ℝ) := (t - 1) ^ 2 / (1 + t ^ 2)
  have huNonneg (t : ℝ) : 0 ≤ u t := by dsimp [u]; positivity
  have huSmooth : ContDiff ℝ ∞ u := by
    dsimp only [u]
    exact (show ContDiff ℝ ∞ (fun t : ℝ => (t - 1) ^ 2) by fun_prop).div
      (show ContDiff ℝ ∞ (fun t : ℝ => 1 + t ^ 2) by fun_prop)
      (fun t => by positivity)
  have huInv (t : ℝ) (ht : 0 < t) : u t⁻¹ = u t := by
    have hd : 1 + t ^ 2 ≠ 0 := by positivity
    dsimp [u]
    field_simp [ht.ne', hd]
    ring
  have huLt (t : ℝ) (ht : 0 < t) : u t < 1 := by
    apply (div_lt_iff₀ (by positivity)).2
    nlinarith only [ht]
  let K := insert (1 : ℝ) (tsupport ψ)
  have hK : IsCompact K := hCompact.isCompact.insert 1
  have hKne : K.Nonempty := insert_nonempty _ _
  obtain ⟨q, hqK, hq⟩ := hK.exists_isMaxOn hKne huSmooth.continuous.continuousOn
  have hqPos : 0 < q := by
    rcases mem_insert_iff.mp hqK with rfl | h
    · norm_num
    · exact hPosSupp h
  let a : ℝ := max (u q) (1 / 2)
  have ha : a < 1 := max_lt (huLt q hqPos) (by norm_num)
  let bump : ContDiffBump (0 : ℝ) :=
    { rIn := a
      rOut := (a + 1) / 2
      rIn_pos := (by norm_num : (0 : ℝ) < 1 / 2).trans_le (le_max_right _ _)
      rIn_lt_rOut := by linarith }
  let g (t : ℝ) := u t * bump (u t)
  have hgNonneg (t : ℝ) : 0 ≤ g t :=
    mul_nonneg (huNonneg t) (bump.nonneg' _)
  have hgSmooth : ContDiff ℝ ∞ g :=
    huSmooth.mul (bump.contDiff.comp huSmooth)
  have hgSupport : tsupport g ⊆ u ⁻¹' closedBall (0 : ℝ) bump.rOut := by
    apply closure_minimal _ (isClosed_closedBall.preimage huSmooth.continuous)
    intro t ht
    have hbu : u t ∈ Function.support bump := by
      intro hn
      exact ht (by simp [g, show bump (u t) = 0 from hn])
    rw [bump.support_eq] at hbu
    exact ball_subset_closedBall hbu
  let δ := 1 - bump.rOut
  have hδ : 0 < δ := by dsimp [δ, bump]; linarith
  have hBounds {t : ℝ} (ht : t ∈ tsupport g) : δ / 2 ≤ t ∧ t ≤ 2 / δ := by
    have hu : u t ≤ bump.rOut := by
      simpa only [mem_preimage, mem_closedBall_zero_iff, Real.norm_eq_abs,
        abs_of_nonneg (huNonneg t)] using hgSupport ht
    have hq := (div_le_iff₀ (by positivity : 0 < 1 + t ^ 2)).mp hu
    have hprod : δ * (1 + t ^ 2) ≤ 2 * t := by
      dsimp [δ]
      nlinarith only [hq]
    have hlo : δ / 2 ≤ t := by nlinarith only [hprod, mul_nonneg hδ.le (sq_nonneg t)]
    have htPos : 0 < t := (half_pos hδ).trans_le hlo
    have hhi : δ * t ≤ 2 := by
      apply le_of_mul_le_mul_right _ htPos
      nlinarith only [hprod, hδ]
    exact ⟨hlo, (le_div_iff₀ hδ).2 (by linarith only [hhi, mul_comm δ t])⟩
  have hgCompact : HasCompactSupport g :=
    isCompact_Icc.of_isClosed_subset (isClosed_tsupport g) fun _ ht => hBounds ht
  have hgPos : tsupport g ⊆ Ioi 0 := fun _ ht => (half_pos hδ).trans_le (hBounds ht).1
  have hgCSupp : tsupport (fun t => (g t : ℂ)) = tsupport g :=
    tsupport_comp_eq (g := Complex.ofReal) (by simp) g
  have hgTest : IsRationalTraceTest (fun t => (g t : ℂ)) := by
    refine ⟨Complex.ofRealCLM.contDiff.comp hgSmooth, ?_, ?_, by simp [g, u]⟩
    · change IsCompact (tsupport (fun t => (g t : ℂ)))
      rw [hgCSupp]
      exact hgCompact.isCompact
    · rw [hgCSupp]
      exact hgPos
  refine ⟨g, bump.rOut, bump.rOut_pos, (sub_pos.mp hδ), hgTest,
    fun t ht => by simp only [g, huInv t ht], hgNonneg, ?_, ?_⟩
  · intro t
    have huPos : 0 < u t ↔ t ≠ 1 := by
      dsimp [u]
      rw [div_pos_iff_of_pos_right (by positivity)]
      constructor
      · rintro h rfl
        norm_num at h
      · intro ht
        exact sq_pos_of_ne_zero (sub_ne_zero.mpr ht)
    have hBumpPos : 0 < bump (u t) ↔ u t < bump.rOut := by
      have he : bump (u t) ≠ 0 ↔ u t < bump.rOut := by
        change u t ∈ Function.support bump ↔ _
        rw [bump.support_eq, mem_ball_zero_iff, Real.norm_eq_abs, abs_of_nonneg (huNonneg t)]
      exact ⟨fun h => he.mp h.ne', fun h =>
        lt_of_le_of_ne (bump.nonneg' _) (Ne.symm (he.mpr h))⟩
    change 0 < u t * bump (u t) ↔ _
    constructor
    · intro h
      have hu' : 0 < u t := lt_of_le_of_ne (huNonneg t) (Ne.symm (left_ne_zero_of_mul h.ne'))
      have hb' : 0 < bump (u t) :=
        lt_of_le_of_ne (bump.nonneg' _) (Ne.symm (right_ne_zero_of_mul h.ne'))
      exact ⟨huPos.mp hu', hBumpPos.mp hb'⟩
    · rintro ⟨ht, hb⟩
      exact mul_pos (huPos.mpr ht) (hBumpPos.mpr hb)
  · intro t ht
    have htr : t ∈ tsupport ψ := hSupport ▸ ht
    exact ((hq (mem_insert_of_mem _ htr)).trans (le_max_left _ _)).trans_lt bump.rIn_lt_rOut

private theorem testMellinConvergent {φ : ℝ → ℂ} (hφ : IsRationalTraceTest φ) (s : ℂ) :
    MellinConvergent φ s := by
  let f (t : ℝ) := (t : ℂ) ^ (s - 1) • φ t
  have hSupport : tsupport f ⊆ tsupport φ := tsupport_smul_subset_right _ _
  have hfCompact : HasCompactSupport f :=
    hφ.2.1.isCompact.of_isClosed_subset (isClosed_tsupport f) hSupport
  have hfContinuous : Continuous f := continuous_iff_continuousAt.mpr fun t => by
    by_cases ht : t ∈ tsupport φ
    · exact (Complex.continuousAt_ofReal_cpow_const t _ (.inr (hφ.2.2.1 ht).ne')).smul
        hφ.1.continuous.continuousAt
    · refine (show ContinuousAt (fun _ : ℝ => (0 : ℂ)) t from continuousAt_const).congr ?_
      filter_upwards [notMem_tsupport_iff_eventuallyEq.mp ht] with x hx
      simp [f, show φ x = 0 from hx]
  exact (hfContinuous.integrable_of_hasCompactSupport hfCompact).integrableOn

theorem MasulloRH.even_real_upper_right_omitted_sum_zero_of_no_boundary_zero_nonneg
    (α : ℝ) (hα : 0 < α) (hα2 : α < 1 / 2)
    (ψ : ℝ → ℝ) (hψ : IsRationalTraceTest (fun t => (ψ t : ℂ)))
    (heven : ∀ t : ℝ, 0 < t → ψ t⁻¹ = ψ t)
    (hNonneg : ∀ t : ℝ, 0 ≤ ψ t)
    (hBoundary : ∀ z : ℂ, riemannZeta z = 0 → z.re = 1 / 2 + α → 0 < z.im → False) :
    ∑' ρ : {ρ : ℂ // riemannZeta ρ = 0 ∧ 1 / 2 + α ≤ ρ.re ∧ ρ.re < 1 ∧ 0 < ρ.im},
      (analyticOrderNatAt riemannZeta (ρ : ℂ) : ℝ) *
        (mellin (fun t => (ψ t : ℂ)) ((ρ : ℂ) - 1 / 2)).re = 0 := by
  obtain ⟨g, r, hr, hr1, hg, hge, hgn, hgStrict, hΨSupp⟩ := intervalTest ψ hψ
  let plus (t : ℝ) := g t + ψ t
  have hp : IsRationalTraceTest (fun t => (plus t : ℂ)) := by
    change IsRationalTraceTest (fun t => ((g t + ψ t : ℝ) : ℂ))
    simp only [Complex.ofReal_add]
    refine ⟨hg.1.add hψ.1, hg.2.1.add hψ.2.1, ?_, ?_⟩
    · exact (tsupport_add _ _).trans (union_subset hg.2.2.1 hψ.2.2.1)
    · have hg1 : (g 1 : ℂ) = 0 := hg.2.2.2
      have hψ1 : (ψ 1 : ℂ) = 0 := hψ.2.2.2
      change (g 1 : ℂ) + (ψ 1 : ℂ) = 0
      rw [hg1, hψ1, add_zero]
  have hpe (t : ℝ) (ht : 0 < t) : plus t⁻¹ = plus t := by simp [plus, hge t ht, heven t ht]
  have hpn (t : ℝ) : 0 ≤ plus t := add_nonneg (hgn t) (hNonneg t)
  have hpStrict (t : ℝ) :
      0 < plus t ↔ t ≠ 1 ∧ (t - 1) ^ 2 / (1 + t ^ 2) < r := by
    refine ⟨?_, fun h => add_pos_of_pos_of_nonneg ((hgStrict t).2 h) (hNonneg t)⟩
    intro h
    by_contra hBad
    have hgZero : g t = 0 := le_antisymm (le_of_not_gt ((hgStrict t).not.mpr hBad)) (hgn t)
    have hΨZero : ψ t = 0 := by
      by_cases ht : t = 1
      · subst t
        exact Complex.ofReal_eq_zero.mp hψ.2.2.2
      · apply Complex.ofReal_eq_zero.mp
        exact image_eq_zero_of_notMem_tsupport (f := fun u : ℝ => (ψ u : ℂ))
          (fun hs => hBad ⟨ht, hΨSupp t hs⟩)
    have : plus t = 0 := by simp [plus, hgZero, hΨZero]
    linarith
  have hPlusZero := even_real_upper_right_omitted_sum_zero_for_interval_positive_test
    α hα hα2 plus hp hpe hpn r hr hr1 hpStrict hBoundary
  have hGZero := even_real_upper_right_omitted_sum_zero_for_interval_positive_test
    α hα hα2 g hg hge hgn r hr hr1 hgStrict hBoundary
  let Z := {ρ : ℂ // riemannZeta ρ = 0 ∧ 1 / 2 + α ≤ ρ.re ∧ ρ.re < 1 ∧ 0 < ρ.im}
  let w (f : ℝ → ℝ) (z : Z) : ℝ :=
    (analyticOrderNatAt riemannZeta (z : ℂ) : ℝ) *
      (mellin (fun t => (f t : ℂ)) ((z : ℂ) - 1 / 2)).re
  have hPlusSummable : Summable (w plus) :=
    (even_test_omitted_sum_eq_four_mul_upper_right α hα plus hp hpe).1
  have hGSummable : Summable (w g) :=
    (even_test_omitted_sum_eq_four_mul_upper_right α hα g hg hge).1
  have hDiff (z : Z) : w ψ z = w plus z - w g z := by
    let s := (z : ℂ) - 1 / 2
    have hFun : (fun t => (ψ t : ℂ)) = (fun t => (plus t : ℂ) - (g t : ℂ)) := by
      funext t
      simp [plus]
    calc
      w ψ z = (analyticOrderNatAt riemannZeta (z : ℂ) : ℝ) *
          (mellin (fun t => (plus t : ℂ) - (g t : ℂ)) s).re := by
        dsimp only [w]
        rw [hFun]
      _ = w plus z - w g z := by
        rw [(hasMellin_sub (testMellinConvergent hp s) (testMellinConvergent hg s)).2,
          Complex.sub_re]
        simp only [w, s, mul_sub]
  change ∑' z : Z, w ψ z = 0
  simp_rw [hDiff]
  rw [hPlusSummable.tsum_sub hGSummable]
  exact sub_eq_zero.mpr (hPlusZero.trans hGZero.symm)

end

-- Step 3: `MasulloRH.even_real_upper_right_omitted_sum_zero_of_no_boundary_zero_nonneg` implies `MasulloRH.even_real_upper_right_omitted_sum_zero_of_no_boundary_zero` (accepted reduction of `MasulloRH.even_real_upper_right_omitted_sum_zero_of_no_boundary_zero`).
section

open MasulloRH MeasureTheory Set Filter Metric
open scoped Topology ContDiff
set_option autoImplicit false

private theorem quadraticBound (f : ℝ → ℝ) (hSmooth : ContDiff ℝ ∞ f)
    (hCompact : HasCompactSupport f) (hOne : f 1 = 0) (hDeriv : deriv f 1 = 0) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x, |f x| ≤ C * (x - 1) ^ 2 := by
  have hD2Compact : HasCompactSupport (iteratedDeriv 2 f) := by
    rw [iteratedDeriv_succ, iteratedDeriv_one]
    exact hCompact.deriv.deriv
  have hTwo : (2 : ℕ∞ω) ≤ ∞ := WithTop.coe_le_coe.mpr le_top
  have hD2Cont := hSmooth.continuous_iteratedDeriv (m := 2) hTwo
  obtain ⟨C, hC⟩ := hD2Cont.norm.bddAbove_range_of_hasCompactSupport
    (hD2Compact.comp_left norm_zero)
  have hNonneg : 0 ≤ C := (norm_nonneg _).trans (hC (mem_range_self 0))
  refine ⟨C, hNonneg, ?_⟩
  intro x
  by_cases hx : x = 1
  · simp [hx, hOne]
  obtain ⟨y, _, hy⟩ := taylor_mean_remainder_lagrange_iteratedDeriv (n := 1) (Ne.symm hx)
    (hSmooth.of_le hTwo).contDiffOn
  have hWithin : derivWithin f (uIcc 1 x) 1 = deriv f 1 :=
    (hSmooth.differentiable (by simp) 1).hasDerivAt.hasDerivWithinAt.derivWithin
      (uniqueDiffOn_uIcc (Ne.symm hx) _ left_mem_uIcc)
  have hTaylor : taylorWithinEval f 1 (uIcc 1 x) 1 x = 0 := by
    rw [show (1 : ℕ) = 0 + 1 by rfl, taylorWithinEval_succ, taylor_within_zero_eval,
      hOne, iteratedDerivWithin_one, hWithin, hDeriv, smul_zero, add_zero]
  rw [hTaylor, sub_zero] at hy
  calc
    |f x| = |iteratedDeriv 2 f y| * (x - 1) ^ 2 / 2 := by
      rw [hy]
      norm_num [abs_div, abs_mul, abs_of_nonneg (sq_nonneg (x - 1))]
    _ ≤ |iteratedDeriv 2 f y| * (x - 1) ^ 2 := by
      exact div_le_self (mul_nonneg (abs_nonneg _) (sq_nonneg _)) (by norm_num)
    _ ≤ C * (x - 1) ^ 2 :=
      mul_le_mul_of_nonneg_right (by simpa only [Real.norm_eq_abs] using hC (mem_range_self y))
        (sq_nonneg _)

private theorem positiveMajorant (ψ : ℝ → ℝ)
    (hψ : IsRationalTraceTest (fun t => (ψ t : ℂ)))
    (heven : ∀ t : ℝ, 0 < t → ψ t⁻¹ = ψ t) :
    ∃ g : ℝ → ℝ, IsRationalTraceTest (fun t => (g t : ℂ)) ∧
      (∀ t : ℝ, 0 < t → g t⁻¹ = g t) ∧ ∀ t, |ψ t| ≤ g t := by
  have hSmooth : ContDiff ℝ ∞ ψ := Complex.reCLM.contDiff.comp hψ.1
  have hSupport : tsupport (fun t => (ψ t : ℂ)) = tsupport ψ :=
    tsupport_comp_eq (g := Complex.ofReal) (by simp) ψ
  have hCompact : HasCompactSupport ψ := by
    change IsCompact (tsupport ψ)
    rw [← hSupport]
    exact hψ.2.1.isCompact
  have hPosSupp : tsupport ψ ⊆ Ioi 0 := by
    rw [← hSupport]
    exact hψ.2.2.1
  have hOne : ψ 1 = 0 := Complex.ofReal_eq_zero.mp hψ.2.2.2
  have hDeriv : deriv ψ 1 = 0 := by
    have hInv : HasDerivAt (fun x : ℝ => x⁻¹) (-1) 1 := by
      simpa using (hasDerivAt_inv (show (1 : ℝ) ≠ 0 by norm_num))
    have hAt : HasDerivAt ψ (deriv ψ 1) 1 :=
      (hSmooth.differentiable (by simp) 1).hasDerivAt
    have hAt' : HasDerivAt ψ (deriv ψ 1) (1 : ℝ)⁻¹ := by simpa using hAt
    have hAtInv : HasDerivAt (fun x : ℝ => ψ x⁻¹) (deriv ψ 1 * -1) 1 := by
      simpa only [inv_one, Function.comp_def] using hAt'.comp 1 hInv
    have hEq : ψ =ᶠ[𝓝 1] (fun x : ℝ => ψ x⁻¹) := by
      filter_upwards [Ioi_mem_nhds (by norm_num : (0 : ℝ) < 1)] with x hx
      exact (heven x hx).symm
    have := (hAtInv.congr_of_eventuallyEq hEq).deriv
    linarith
  obtain ⟨C, hC, hQuad⟩ := quadraticBound ψ hSmooth hCompact hOne hDeriv

  -- This smooth coordinate is inversion-invariant on the positive reals.
  let u (t : ℝ) := (t - 1) ^ 2 / (1 + t ^ 2)
  have huNonneg (t : ℝ) : 0 ≤ u t := by dsimp [u]; positivity
  have huSmooth : ContDiff ℝ ∞ u := by
    dsimp only [u]
    exact (show ContDiff ℝ ∞ (fun t : ℝ => (t - 1) ^ 2) by fun_prop).div
      (show ContDiff ℝ ∞ (fun t : ℝ => 1 + t ^ 2) by fun_prop)
      (fun t => by positivity)
  have huInv (t : ℝ) (ht : 0 < t) : u t⁻¹ = u t := by
    have hd : 1 + t ^ 2 ≠ 0 := by positivity
    dsimp [u]
    field_simp [ht.ne', hd]
    ring
  have huLt (t : ℝ) (ht : 0 < t) : u t < 1 := by
    apply (div_lt_iff₀ (by positivity)).2
    nlinarith only [ht]
  let K := insert (1 : ℝ) (tsupport ψ)
  have hK : IsCompact K := hCompact.isCompact.insert 1
  have hKne : K.Nonempty := insert_nonempty _ _
  obtain ⟨q, hqK, hq⟩ := hK.exists_isMaxOn hKne huSmooth.continuous.continuousOn
  have hqPos : 0 < q := by
    rcases mem_insert_iff.mp hqK with rfl | h
    · norm_num
    · exact hPosSupp h
  let a : ℝ := max (u q) (1 / 2)
  have ha : a < 1 := max_lt (huLt q hqPos) (by norm_num)
  let bump : ContDiffBump (0 : ℝ) :=
    { rIn := a
      rOut := (a + 1) / 2
      rIn_pos := (by norm_num : (0 : ℝ) < 1 / 2).trans_le (le_max_right _ _)
      rIn_lt_rOut := by linarith }
  have hBumpOne (t : ℝ) (ht : t ∈ tsupport ψ) : bump (u t) = 1 := by
    apply bump.one_of_mem_closedBall
    rw [mem_closedBall_zero_iff, Real.norm_eq_abs, abs_of_nonneg (huNonneg t)]
    exact (hq (mem_insert_of_mem _ ht)).trans (le_max_left _ _)
  obtain ⟨p, _, hp⟩ := hK.exists_isMaxOn hKne
    (show Continuous (fun t : ℝ => 1 + t ^ 2) by fun_prop).continuousOn
  let B := C * (1 + p ^ 2)
  have hB : 0 ≤ B := by dsimp [B]; positivity
  let g (t : ℝ) := B * u t * bump (u t)
  have hgNonneg (t : ℝ) : 0 ≤ g t :=
    mul_nonneg (mul_nonneg hB (huNonneg t)) (bump.nonneg' _)
  have hgSmooth : ContDiff ℝ ∞ g :=
    (contDiff_const.mul huSmooth).mul (bump.contDiff.comp huSmooth)
  have hgSupport : tsupport g ⊆ u ⁻¹' closedBall (0 : ℝ) bump.rOut := by
    apply closure_minimal _ (isClosed_closedBall.preimage huSmooth.continuous)
    intro t ht
    have hbu : u t ∈ Function.support bump := by
      intro hn
      exact ht (by simp [g, show bump (u t) = 0 from hn])
    rw [bump.support_eq] at hbu
    exact ball_subset_closedBall hbu
  let δ := 1 - bump.rOut
  have hδ : 0 < δ := by dsimp [δ, bump]; linarith
  have hBounds {t : ℝ} (ht : t ∈ tsupport g) : δ / 2 ≤ t ∧ t ≤ 2 / δ := by
    have hu : u t ≤ bump.rOut := by
      simpa only [mem_preimage, mem_closedBall_zero_iff, Real.norm_eq_abs,
        abs_of_nonneg (huNonneg t)] using hgSupport ht
    have hq := (div_le_iff₀ (by positivity : 0 < 1 + t ^ 2)).mp hu
    have hprod : δ * (1 + t ^ 2) ≤ 2 * t := by
      dsimp [δ]
      nlinarith only [hq]
    have hlo : δ / 2 ≤ t := by nlinarith only [hprod, mul_nonneg hδ.le (sq_nonneg t)]
    have htPos : 0 < t := (half_pos hδ).trans_le hlo
    have hhi : δ * t ≤ 2 := by
      apply le_of_mul_le_mul_right _ htPos
      nlinarith only [hprod, hδ]
    exact ⟨hlo, (le_div_iff₀ hδ).2 (by linarith only [hhi, mul_comm δ t])⟩
  have hgCompact : HasCompactSupport g :=
    isCompact_Icc.of_isClosed_subset (isClosed_tsupport g) fun _ ht => hBounds ht
  have hgPos : tsupport g ⊆ Ioi 0 := fun _ ht => (half_pos hδ).trans_le (hBounds ht).1
  have hgCSupp : tsupport (fun t => (g t : ℂ)) = tsupport g :=
    tsupport_comp_eq (g := Complex.ofReal) (by simp) g
  have hgTest : IsRationalTraceTest (fun t => (g t : ℂ)) := by
    refine ⟨Complex.ofRealCLM.contDiff.comp hgSmooth, ?_, ?_, by simp [g, u]⟩
    · change IsCompact (tsupport (fun t => (g t : ℂ)))
      rw [hgCSupp]
      exact hgCompact.isCompact
    · rw [hgCSupp]
      exact hgPos
  refine ⟨g, hgTest, fun t ht => by simp only [g, huInv t ht], ?_⟩
  intro t
  by_cases ht : t ∈ tsupport ψ
  · have hpt : 1 + t ^ 2 ≤ 1 + p ^ 2 := hp (mem_insert_of_mem _ ht)
    have hBU : C * (t - 1) ^ 2 ≤ B * u t := by
      dsimp [u, B]
      have hd : 0 < 1 + t ^ 2 := by positivity
      rw [← mul_div_assoc]
      refine (le_div_iff₀ hd).2 ?_
      calc
        C * (t - 1) ^ 2 * (1 + t ^ 2) ≤ C * (t - 1) ^ 2 * (1 + p ^ 2) :=
          mul_le_mul_of_nonneg_left hpt (mul_nonneg hC (sq_nonneg _))
        _ = C * (1 + p ^ 2) * (t - 1) ^ 2 := by ring
    exact (hQuad t).trans (by simpa only [g, hBumpOne t ht, mul_one] using hBU)
  · simpa only [image_eq_zero_of_notMem_tsupport ht, abs_zero] using hgNonneg t

private theorem testMellinConvergent_p3 {φ : ℝ → ℂ} (hφ : IsRationalTraceTest φ) (s : ℂ) :
    MellinConvergent φ s := by
  let f (t : ℝ) := (t : ℂ) ^ (s - 1) • φ t
  have hSupport : tsupport f ⊆ tsupport φ := tsupport_smul_subset_right _ _
  have hfCompact : HasCompactSupport f :=
    hφ.2.1.isCompact.of_isClosed_subset (isClosed_tsupport f) hSupport
  have hfContinuous : Continuous f := continuous_iff_continuousAt.mpr fun t => by
    by_cases ht : t ∈ tsupport φ
    · exact (Complex.continuousAt_ofReal_cpow_const t _ (.inr (hφ.2.2.1 ht).ne')).smul
        hφ.1.continuous.continuousAt
    · refine (show ContinuousAt (fun _ : ℝ => (0 : ℂ)) t from continuousAt_const).congr ?_
      filter_upwards [notMem_tsupport_iff_eventuallyEq.mp ht] with x hx
      simp [f, show φ x = 0 from hx]
  exact (hfContinuous.integrable_of_hasCompactSupport hfCompact).integrableOn

theorem MasulloRH.even_real_upper_right_omitted_sum_zero_of_no_boundary_zero
    (α : ℝ) (hα : 0 < α) (hα2 : α < 1 / 2)
    (ψ : ℝ → ℝ) (hψ : IsRationalTraceTest (fun t => (ψ t : ℂ)))
    (heven : ∀ t : ℝ, 0 < t → ψ t⁻¹ = ψ t)
    (hBoundary : ∀ z : ℂ, riemannZeta z = 0 → z.re = 1 / 2 + α → 0 < z.im → False) :
    ∑' ρ : {ρ : ℂ // riemannZeta ρ = 0 ∧ 1 / 2 + α ≤ ρ.re ∧ ρ.re < 1 ∧ 0 < ρ.im},
      (analyticOrderNatAt riemannZeta (ρ : ℂ) : ℝ) *
        (mellin (fun t => (ψ t : ℂ)) ((ρ : ℂ) - 1 / 2)).re = 0 := by
  obtain ⟨g, hg, hge, hDom⟩ := positiveMajorant ψ hψ heven
  let plus (t : ℝ) := g t + ψ t
  have hp : IsRationalTraceTest (fun t => (plus t : ℂ)) := by
    change IsRationalTraceTest (fun t => ((g t + ψ t : ℝ) : ℂ))
    simp only [Complex.ofReal_add]
    refine ⟨hg.1.add hψ.1, hg.2.1.add hψ.2.1, ?_, ?_⟩
    · exact (tsupport_add _ _).trans (union_subset hg.2.2.1 hψ.2.2.1)
    · have hg1 : (g 1 : ℂ) = 0 := hg.2.2.2
      have hψ1 : (ψ 1 : ℂ) = 0 := hψ.2.2.2
      change (g 1 : ℂ) + (ψ 1 : ℂ) = 0
      rw [hg1, hψ1, add_zero]
  have hpe (t : ℝ) (ht : 0 < t) : plus t⁻¹ = plus t := by simp [plus, hge t ht, heven t ht]
  have hpn (t : ℝ) : 0 ≤ plus t := by linarith [(neg_le_abs (ψ t)).trans (hDom t)]
  have hgn (t : ℝ) : 0 ≤ g t := (abs_nonneg _).trans (hDom t)
  have hPlusZero := even_real_upper_right_omitted_sum_zero_of_no_boundary_zero_nonneg
    α hα hα2 plus hp hpe hpn hBoundary
  have hGZero := even_real_upper_right_omitted_sum_zero_of_no_boundary_zero_nonneg
    α hα hα2 g hg hge hgn hBoundary
  let Z := {ρ : ℂ // riemannZeta ρ = 0 ∧ 1 / 2 + α ≤ ρ.re ∧ ρ.re < 1 ∧ 0 < ρ.im}
  let w (f : ℝ → ℝ) (z : Z) : ℝ :=
    (analyticOrderNatAt riemannZeta (z : ℂ) : ℝ) *
      (mellin (fun t => (f t : ℂ)) ((z : ℂ) - 1 / 2)).re
  have hPlusSummable : Summable (w plus) :=
    (even_test_omitted_sum_eq_four_mul_upper_right α hα plus hp hpe).1
  have hGSummable : Summable (w g) :=
    (even_test_omitted_sum_eq_four_mul_upper_right α hα g hg hge).1
  have hDiff (z : Z) : w ψ z = w plus z - w g z := by
    let s := (z : ℂ) - 1 / 2
    have hFun : (fun t => (ψ t : ℂ)) = (fun t => (plus t : ℂ) - (g t : ℂ)) := by
      funext t
      simp [plus]
    calc
      w ψ z = (analyticOrderNatAt riemannZeta (z : ℂ) : ℝ) *
          (mellin (fun t => (plus t : ℂ) - (g t : ℂ)) s).re := by
        dsimp only [w]
        rw [hFun]
      _ = w plus z - w g z := by
        rw [(hasMellin_sub (testMellinConvergent_p3 hp s) (testMellinConvergent_p3 hg s)).2,
          Complex.sub_re]
        simp only [w, s, mul_sub]
  change ∑' z : Z, w ψ z = 0
  simp_rw [hDiff]
  rw [hPlusSummable.tsum_sub hGSummable]
  exact sub_eq_zero.mpr (hPlusZero.trans hGZero.symm)

end

-- Step 4: `MasulloRH.even_real_upper_right_omitted_sum_zero_of_no_boundary_zero` implies `MasulloRH.even_real_upper_right_omitted_sum_zero` (accepted reduction of `MasulloRH.even_real_upper_right_omitted_sum_zero`).
section

open MasulloRH MeasureTheory Set Filter
open scoped Topology
set_option autoImplicit false

theorem MasulloRH.even_real_upper_right_omitted_sum_zero
    (α : ℝ) (hα : 0 < α) (hα2 : α < 1 / 2)
    (ψ : ℝ → ℝ) (hψ : IsRationalTraceTest (fun t => (ψ t : ℂ)))
    (heven : ∀ t : ℝ, 0 < t → ψ t⁻¹ = ψ t) :
    ∑' ρ : {ρ : ℂ // riemannZeta ρ = 0 ∧ 1 / 2 + α ≤ ρ.re ∧ ρ.re < 1 ∧ 0 < ρ.im},
      (analyticOrderNatAt riemannZeta (ρ : ℂ) : ℝ) *
        (mellin (fun t => (ψ t : ℂ)) ((ρ : ℂ) - 1 / 2)).re = 0 := by
  classical
  let Z (β : ℝ) := {z : ℂ // riemannZeta z = 0 ∧
    1 / 2 + β ≤ z.re ∧ z.re < 1 ∧ 0 < z.im}
  let weight : ℂ → ℝ := fun z =>
    (analyticOrderNatAt riemannZeta z : ℝ) *
      (mellin (fun t => (ψ t : ℂ)) (z - 1 / 2)).re
  have hSummable : Summable (fun z : Z (α / 2) => weight z) :=
    (even_test_omitted_sum_eq_four_mul_upper_right (α / 2)
      (half_pos hα) ψ hψ heven).1
  let cut (β : ℝ) (z : Z (α / 2)) : ℝ :=
    if 1 / 2 + β ≤ (z : ℂ).re then weight z else 0
  have hSum (β : ℝ) (hβ : α / 2 ≤ β) :
      (∑' z : Z β, weight z) = ∑' z : Z (α / 2), cut β z := by
    let s : Set (Z (α / 2)) := {z | 1 / 2 + β ≤ (z : ℂ).re}
    let e : Z β ≃ s :=
      { toFun := fun z =>
          ⟨⟨z, z.property.1, (add_le_add_right hβ _).trans z.property.2.1,
            z.property.2.2⟩, z.property.2.1⟩
        invFun := fun z => ⟨z.val, z.val.property.1, z.property, z.val.property.2.2⟩
        left_inv := fun _ => rfl
        right_inv := fun _ => rfl }
    calc
      (∑' z : Z β, weight z) = ∑' z : s, weight z.val :=
        e.tsum_eq (fun z : s => weight z.val)
      _ = ∑' z : Z (α / 2), cut β z := by
        simpa only [Set.indicator_apply, cut, s, Set.mem_ofPred_eq] using
          (tsum_subtype s (fun z : Z (α / 2) => weight z))

  let bad : Set ℝ := (fun z : ℂ => z.re - 1 / 2) '' riemannZetaZeros
  have hZeros : riemannZetaZeros.Countable :=
    (HereditarilyLindelofSpace.isLindelof riemannZetaZeros).countable_of_isDiscrete
      isDiscrete_riemannZetaZeros
  have hDense : Dense badᶜ := (hZeros.image _).dense_compl ℝ
  let good := Ioo (α / 2) α ∩ badᶜ
  have hClosure : α ∈ closure good := by
    rw [Real.mem_closure_iff]
    intro ε hε
    let lower := max (α / 2) (α - ε)
    have hLower : lower < α := max_lt (by linarith) (by linarith)
    obtain ⟨β, hβ, hNotBad⟩ :=
      hDense.inter_open_nonempty (Ioo lower α) isOpen_Ioo (nonempty_Ioo.mpr hLower)
    have hDist : |β - α| < ε := by
      have hLeft : α - ε < β := (le_max_right _ _).trans_lt hβ.1
      rw [abs_of_neg (sub_neg.mpr hβ.2)]
      linarith
    exact ⟨β, ⟨⟨(le_max_left _ _).trans_lt hβ.1, hβ.2⟩, hNotBad⟩, hDist⟩

  let F := 𝓝[good] α
  have : F.NeBot := mem_closure_iff_nhdsWithin_neBot.mp hClosure
  have hGood : ∀ᶠ β in F, β ∈ good := self_mem_nhdsWithin
  have hPointwise (z : Z (α / 2)) : Tendsto (fun β => cut β z) F (𝓝 (cut α z)) := by
    by_cases hz : 1 / 2 + α ≤ (z : ℂ).re
    · refine tendsto_const_nhds.congr' ?_
      filter_upwards [hGood] with β hβ
      have hβz : 1 / 2 + β ≤ (z : ℂ).re :=
        (add_le_add_right hβ.1.2.le _).trans hz
      simp only [cut, hβz, hz, ↓reduceIte]
    · have hLt : (z : ℂ).re - 1 / 2 < α := by linarith [lt_of_not_ge hz]
      have hEventually : ∀ᶠ β in F, β ∈ Ioi ((z : ℂ).re - 1 / 2) :=
        nhdsWithin_le_nhds (Ioi_mem_nhds hLt)
      refine tendsto_const_nhds.congr' ?_
      filter_upwards [hEventually] with β hβ
      have hβz : ¬ 1 / 2 + β ≤ (z : ℂ).re := by
        have : (z : ℂ).re - 1 / 2 < β := hβ
        linarith
      simp only [cut, hβz, hz, ↓reduceIte]
  have hLimit : Tendsto (fun β => ∑' z, cut β z) F (𝓝 (∑' z, cut α z)) := by
    apply tendsto_tsum_of_dominated_convergence hSummable.norm hPointwise
    exact Eventually.of_forall fun β z => by
      dsimp only [cut]
      by_cases hz : 1 / 2 + β ≤ (z : ℂ).re
      · rw [if_pos hz]
      · rw [if_neg hz, norm_zero]
        exact norm_nonneg _
  have hZero : (fun _ : ℝ => (0 : ℝ)) =ᶠ[F] (fun β => ∑' z, cut β z) := by
    filter_upwards [hGood] with β hβ
    rw [← hSum β hβ.1.1.le]
    symm
    apply even_real_upper_right_omitted_sum_zero_of_no_boundary_zero β
      ((half_pos hα).trans hβ.1.1) (hβ.1.2.trans hα2) ψ hψ heven
    intro z hz hRe _
    exact hβ.2 ⟨z, mem_riemannZetaZeros.mpr hz, by linarith⟩
  change (∑' z : Z α, weight z) = 0
  rw [hSum α (by linarith)]
  exact tendsto_nhds_unique hLimit (tendsto_const_nhds.congr' hZero)

end

-- Step 5: `MasulloRH.even_real_upper_right_omitted_sum_zero` implies `MasulloRH.trace_formula_inversion_even` (accepted reduction of `MasulloRH.trace_formula_inversion_even`).
section

set_option autoImplicit false

namespace MasulloRH_EvenReduction

open MeasureTheory Set Filter Complex
open scoped Topology ContDiff

private lemma test_comp_clm {φ : ℝ → ℂ} (hφ : MasulloRH.IsRationalTraceTest φ)
    (L : ℂ →L[ℝ] ℂ) : MasulloRH.IsRationalTraceTest (L ∘ φ) := by
  rcases hφ with ⟨hSmooth, hCpt, hSupp, hOne⟩
  refine ⟨L.contDiff.comp hSmooth, hCpt.comp_left (map_zero L), ?_, ?_⟩
  · exact (tsupport_comp_subset (map_zero L) φ).trans hSupp
  · show L (φ 1) = 0
    rw [hOne, map_zero]

private lemma test_mellinConvergent {φ : ℝ → ℂ} (hφ : MasulloRH.IsRationalTraceTest φ) (s : ℂ) :
    MellinConvergent φ s := by
  rcases hφ with ⟨hSmooth, hCpt, hSupp, _⟩
  unfold MellinConvergent
  simp only [smul_eq_mul]
  have hg_cont : Continuous (fun t : ℝ => (t : ℂ) ^ (s - 1) * φ t) := by
    rw [continuous_iff_continuousAt]
    intro x
    by_cases hx : 0 < x
    · exact (Complex.continuousAt_ofReal_cpow_const x (s - 1) (Or.inr (ne_of_gt hx))).mul
        hSmooth.continuous.continuousAt
    · have hx_not_supp : x ∉ tsupport φ := fun hmem => hx (hSupp hmem)
      have h_zero : φ =ᶠ[𝓝 x] 0 := notMem_tsupport_iff_eventuallyEq.mp hx_not_supp
      have hg_zero : (fun t : ℝ => (t : ℂ) ^ (s - 1) * φ t) =ᶠ[𝓝 x] (fun _ => (0 : ℂ)) :=
        h_zero.mono (fun y (hy : φ y = 0) => by dsimp; rw [hy, mul_zero])
      exact continuousAt_const.congr hg_zero.symm
  have hg_cpt : HasCompactSupport (fun t : ℝ => (t : ℂ) ^ (s - 1) * φ t) :=
    hCpt.mul_left
  exact (hg_cont.integrable_of_hasCompactSupport hg_cpt).integrableOn

private lemma test_mellin_re_add_im {φ : ℝ → ℂ} (hφ : MasulloRH.IsRationalTraceTest φ) (s : ℂ) :
    mellin φ s = mellin (fun t => ((φ t).re : ℂ)) s + Complex.I * mellin (fun t => ((φ t).im : ℂ)) s := by
  have hφ_re : MasulloRH.IsRationalTraceTest (fun t => ((φ t).re : ℂ)) :=
    test_comp_clm hφ (Complex.ofRealCLM.comp Complex.reCLM)
  have hφ_im : MasulloRH.IsRationalTraceTest (fun t => ((φ t).im : ℂ)) :=
    test_comp_clm hφ (Complex.ofRealCLM.comp Complex.imCLM)
  have hInt_re : IntegrableOn (fun t : ℝ => (t : ℂ) ^ (s - 1) * ((φ t).re : ℂ)) (Ioi 0) := by
    simpa only [MellinConvergent, smul_eq_mul] using test_mellinConvergent hφ_re s
  have hInt_im : IntegrableOn (fun t : ℝ => (t : ℂ) ^ (s - 1) * ((φ t).im : ℂ)) (Ioi 0) := by
    simpa only [MellinConvergent, smul_eq_mul] using test_mellinConvergent hφ_im s
  simp only [mellin, smul_eq_mul]
  have hdecomp : (fun t : ℝ => (t : ℂ) ^ (s - 1) * φ t) =
      (fun t : ℝ =>
        (t : ℂ) ^ (s - 1) * ((φ t).re : ℂ) +
          Complex.I * ((t : ℂ) ^ (s - 1) * ((φ t).im : ℂ))) := by
    funext t
    conv_lhs => rw [← Complex.re_add_im (φ t)]
    ring
  rw [hdecomp, MeasureTheory.integral_add hInt_re (hInt_im.const_mul Complex.I),
      MeasureTheory.integral_const_mul]

end MasulloRH_EvenReduction

open MasulloRH MeasureTheory Set

theorem MasulloRH.trace_formula_inversion_even (α : ℝ) (hα : 0 < α) (φ : ℝ → ℂ) (hφ : IsRationalTraceTest φ)
    (heven : ∀ t : ℝ, 0 < t → φ t⁻¹ = φ t) :
    IntegrableOn (realTraceIntegrand φ) (Ioi 1) ∧
    Summable (primePowerTraceTerm φ) ∧ Summable (zetaTraceTerm φ α) ∧
    (∫ t in Ioi (1 : ℝ), realTraceIntegrand φ t) +
      (∑' i : Nat.Primes × ℕ, primePowerTraceTerm φ i) =
      mellin φ (1 / 2) + mellin φ (-1 / 2) -
        ∑' ρ : ZetaZerosInTraceStrip α, zetaTraceTerm φ α ρ := by
  by_cases hα_half : 1 / 2 ≤ α
  · exact MasulloAudit.trace_formula_rational_of_half_le α hα_half φ hφ
  · have hα_lt : α < 1 / 2 := lt_of_not_ge hα_half
    have hWin := MasulloAudit.trace_formula_window_with_remainder α φ hφ
    rcases hWin with ⟨hInt, hSumP, hSumZ, _, hEq⟩
    refine ⟨hInt, hSumP, hSumZ, ?_⟩
    let remainder := {ρ : ZetaZerosInTraceStrip (1 / 2) | α ≤ |(ρ : ℂ).re - 1 / 2|}
    suffices hRemZero : (∑' ρ : remainder, zetaTraceTerm φ (1 / 2) ρ) = 0 by
      rw [hRemZero, sub_zero] at hEq
      exact hEq
    let ψ_re : ℝ → ℝ := fun t => (φ t).re
    let ψ_im : ℝ → ℝ := fun t => (φ t).im
    let φ_re : ℝ → ℂ := fun t => (ψ_re t : ℂ)
    let φ_im : ℝ → ℂ := fun t => (ψ_im t : ℂ)
    have hφ_re : IsRationalTraceTest φ_re :=
      MasulloRH_EvenReduction.test_comp_clm hφ (Complex.ofRealCLM.comp Complex.reCLM)
    have hφ_im : IsRationalTraceTest φ_im :=
      MasulloRH_EvenReduction.test_comp_clm hφ (Complex.ofRealCLM.comp Complex.imCLM)
    have heven_re : ∀ t : ℝ, 0 < t → ψ_re t⁻¹ = ψ_re t :=
      fun t ht => congrArg Complex.re (heven t ht)
    have heven_im : ∀ t : ℝ, 0 < t → ψ_im t⁻¹ = ψ_im t :=
      fun t ht => congrArg Complex.im (heven t ht)
    have hSumRem_re : Summable (fun ρ : remainder => zetaTraceTerm φ_re (1 / 2) ρ) :=
      (MasulloAudit.trace_formula_window_with_remainder α φ_re hφ_re).2.2.2.1
    have hSumRem_im : Summable (fun ρ : remainder => zetaTraceTerm φ_im (1 / 2) ρ) :=
      (MasulloAudit.trace_formula_window_with_remainder α φ_im hφ_im).2.2.2.1
    have hTerm_decomp : (fun ρ : remainder => zetaTraceTerm φ (1 / 2) ρ) =
        (fun ρ : remainder =>
          zetaTraceTerm φ_re (1 / 2) ρ + Complex.I * zetaTraceTerm φ_im (1 / 2) ρ) := by
      funext ρ
      dsimp [zetaTraceTerm]
      rw [MasulloRH_EvenReduction.test_mellin_re_add_im hφ ((ρ : ℂ) - 1 / 2)]
      ring
    rw [hTerm_decomp, hSumRem_re.tsum_add (hSumRem_im.mul_left Complex.I), tsum_mul_left]
    have hSymm_re := (MasulloRH.even_test_omitted_sum_eq_four_mul_upper_right α hα ψ_re hφ_re heven_re).2
    have hSymm_im := (MasulloRH.even_test_omitted_sum_eq_four_mul_upper_right α hα ψ_im hφ_im heven_im).2
    have hChild_re := MasulloRH.even_real_upper_right_omitted_sum_zero α hα hα_lt ψ_re hφ_re heven_re
    have hChild_im := MasulloRH.even_real_upper_right_omitted_sum_zero α hα hα_lt ψ_im hφ_im heven_im
    rw [hSymm_re, hChild_re, hSymm_im, hChild_im]
    simp

end

-- Step 6: `MasulloRH.trace_formula_inversion_even` implies `MasulloAudit.trace_formula_rational_source_form` (accepted reduction of `MasulloAudit.trace_formula_rational_source_form`).
section

open MasulloRH MeasureTheory Set Filter
open scoped Topology ContDiff

private theorem test_inv {φ : ℝ → ℂ} (hφ : IsRationalTraceTest φ) :
    IsRationalTraceTest (fun t => φ t⁻¹) := by
  let K := Inv.inv '' tsupport φ
  have hK : IsCompact K := hφ.2.1.image_of_continuousOn
    (continuousOn_id.inv₀ fun x hx => ne_of_gt (hφ.2.2.1 hx))
  have hs : tsupport (fun t => φ t⁻¹) ⊆ K := by
    apply closure_minimal _ hK.isClosed
    intro x hx
    exact ⟨x⁻¹, subset_tsupport φ hx, inv_inv x⟩
  have hpos : K ⊆ Ioi (0 : ℝ) := by
    rintro x ⟨y, hy, rfl⟩
    change 0 < y⁻¹
    exact inv_pos.mpr (show 0 < y from hφ.2.2.1 hy)
  refine ⟨?_, hK.of_isClosed_subset (isClosed_tsupport _) hs, hs.trans hpos, ?_⟩
  · rw [contDiff_iff_contDiffAt]
    intro x
    by_cases hx : x ∈ tsupport (fun t => φ t⁻¹)
    · exact hφ.1.contDiffAt.comp x (contDiffAt_inv ℝ (ne_of_gt (hpos (hs hx))))
    · exact contDiffAt_const.congr_of_eventuallyEq
        (notMem_tsupport_iff_eventuallyEq.mp hx)
  · simpa using hφ.2.2.2

private theorem test_add {φ ψ : ℝ → ℂ}
    (hφ : IsRationalTraceTest φ) (hψ : IsRationalTraceTest ψ) :
    IsRationalTraceTest (fun t => φ t + ψ t) := by
  refine ⟨hφ.1.add hψ.1, hφ.2.1.add hψ.2.1,
    (tsupport_add φ ψ).trans (union_subset hφ.2.2.1 hψ.2.2.1), ?_⟩
  simp [hφ.2.2.2, hψ.2.2.2]

private theorem test_sub {φ ψ : ℝ → ℂ}
    (hφ : IsRationalTraceTest φ) (hψ : IsRationalTraceTest ψ) :
    IsRationalTraceTest (fun t => φ t - ψ t) := by
  refine ⟨hφ.1.sub hψ.1, hφ.2.1.sub hψ.2.1,
    (tsupport_sub φ ψ).trans (union_subset hφ.2.2.1 hψ.2.2.1), ?_⟩
  simp [hφ.2.2.2, hψ.2.2.2]

private theorem test_half {φ : ℝ → ℂ} (hφ : IsRationalTraceTest φ) :
    IsRationalTraceTest (fun t => φ t / 2) := by
  refine ⟨hφ.1.div_const 2, ?_, ?_, by simp [hφ.2.2.2]⟩
  · exact hφ.2.1.comp_left (g := fun z : ℂ => z / 2) (by simp)
  · exact (tsupport_comp_subset (g := fun z : ℂ => z / 2) (by simp) φ).trans hφ.2.2.1

private theorem test_mellin {φ : ℝ → ℂ} (hφ : IsRationalTraceTest φ) (s : ℂ) :
    MellinConvergent φ s := by
  let f := fun t : ℝ => (t : ℂ) ^ (s - 1) * φ t
  have hs : tsupport f ⊆ tsupport φ := tsupport_mul_subset_right
  have hc : Continuous f := by
    apply continuous_of_tsupport
    intro t ht
    have hp : 0 < t := hφ.2.2.1 (hs ht)
    exact (Complex.continuousAt_ofReal_cpow_const t (s - 1)
      (Or.inr (ne_of_gt hp))).mul hφ.1.continuous.continuousAt
  have hk : HasCompactSupport f := hφ.2.1.mul_left
  exact (hc.integrable_of_hasCompactSupport hk).integrableOn

-- Linearity combines the even case with the already proved odd case.
theorem trace_formula_of_inversion_even
    (H : ∀ (α : ℝ), 0 < α → ∀ (φ : ℝ → ℂ), IsRationalTraceTest φ →
      (∀ t : ℝ, 0 < t → φ t⁻¹ = φ t) →
      IntegrableOn (realTraceIntegrand φ) (Ioi 1) ∧
      Summable (primePowerTraceTerm φ) ∧ Summable (zetaTraceTerm φ α) ∧
      (∫ t in Ioi (1 : ℝ), realTraceIntegrand φ t) +
        (∑' i : Nat.Primes × ℕ, primePowerTraceTerm φ i) =
        mellin φ (1 / 2) + mellin φ (-1 / 2) -
          ∑' ρ : ZetaZerosInTraceStrip α, zetaTraceTerm φ α ρ)
    (α : ℝ) (hα : 0 < α) (φ : ℝ → ℂ) (hφ : IsRationalTraceTest φ) :
    IntegrableOn (realTraceIntegrand φ) (Ioi 1) ∧
      Summable (primePowerTraceTerm φ) ∧ Summable (zetaTraceTerm φ α) ∧
      (∫ t in Ioi (1 : ℝ), realTraceIntegrand φ t) +
        (∑' i : Nat.Primes × ℕ, primePowerTraceTerm φ i) =
        mellin φ (1 / 2) + mellin φ (-1 / 2) -
          ∑' ρ : ZetaZerosInTraceStrip α, zetaTraceTerm φ α ρ := by
  let e : ℝ → ℂ := fun t => (φ t + φ t⁻¹) / 2
  let o : ℝ → ℂ := fun t => φ t - e t
  have he : IsRationalTraceTest e := test_half (test_add hφ (test_inv hφ))
  have ho : IsRationalTraceTest o := test_sub hφ he
  have heven : ∀ t : ℝ, 0 < t → e t⁻¹ = e t := by
    intro t _; dsimp [e]; rw [inv_inv, add_comm]
  have hodd : ∀ t : ℝ, 0 < t → o t⁻¹ = -o t := by
    intro t _; dsimp [o, e]; rw [inv_inv]; ring
  obtain ⟨heI, heP, heZ, heq⟩ := H α hα e he heven
  obtain ⟨hoI, hoP, hoZ, hoq⟩ := trace_formula_inversion_odd α hα o ho hodd
  have hdecomp : φ = fun t => e t + o t := by funext t; dsimp [o]; ring
  have hI : realTraceIntegrand φ = fun t => realTraceIntegrand e t + realTraceIntegrand o t := by
    funext t; simp only [realTraceIntegrand, hdecomp]; ring
  have hP : primePowerTraceTerm φ = fun i => primePowerTraceTerm e i + primePowerTraceTerm o i := by
    funext i; simp only [primePowerTraceTerm, hdecomp]; ring
  have hM (s : ℂ) : mellin φ s = mellin e s + mellin o s := by
    rw [hdecomp]
    exact (hasMellin_add (test_mellin he s) (test_mellin ho s)).2
  have hZ : zetaTraceTerm φ α = fun ρ => zetaTraceTerm e α ρ + zetaTraceTerm o α ρ := by
    funext ρ; simp only [zetaTraceTerm, hM, mul_add]
  refine ⟨hI ▸ heI.add hoI, hP ▸ heP.add hoP, hZ ▸ heZ.add hoZ, ?_⟩
  rw [hI, hP, hZ, integral_add heI hoI, heP.tsum_add hoP, heZ.tsum_add hoZ,
    hM, hM]
  linear_combination heq + hoq

local instance factPrimes (p : Nat.Primes) : Fact (p : ℕ).Prime := ⟨p.2⟩

theorem MasulloAudit.trace_formula_rational_source_form (α : ℝ) (hα : 0 < α) (φ : ℝ → ℂ)
    (hφ : IsRationalTraceTest φ)
    (inst : ∀ p : Nat.Primes, MeasurableSpace ℚ_[p])
    [hB : ∀ p : Nat.Primes, BorelSpace ℚ_[p]]
    (μ : ∀ p : Nat.Primes, Measure ℚ_[p]) [hμ : ∀ p : Nat.Primes, (μ p).IsAddHaarMeasure] :
    IntegrableOn (fun x : ℝ => φ |x| * ((|x| ^ (1/2 : ℝ) / |1 - x| * (1 / |x|) : ℝ) : ℂ))
        {x : ℝ | x ≠ 0} ∧
    (∀ p : Nat.Primes,
      IntegrableOn (fun g : ℚ_[p] => φ ‖g‖ * ((‖g‖ ^ (1/2 : ℝ) / ‖1 - g‖ * (1 / ‖g‖) : ℝ) : ℂ))
        {g : ℚ_[p] | g ≠ 0} (μ p)) ∧
    Summable (fun p : Nat.Primes =>
      ((Real.log p / (μ p).real {g : ℚ_[p] | ‖g‖ = 1} : ℝ) : ℂ) *
        ∫ g in {g : ℚ_[p] | g ≠ 0},
          φ ‖g‖ * ((‖g‖ ^ (1/2 : ℝ) / ‖1 - g‖ * (1 / ‖g‖) : ℝ) : ℂ) ∂(μ p)) ∧
    Summable (zetaTraceTerm φ α) ∧
    (1/2 : ℂ) * (∫ x in {x : ℝ | x ≠ 0},
        φ |x| * ((|x| ^ (1/2 : ℝ) / |1 - x| * (1 / |x|) : ℝ) : ℂ)) +
      ∑' p : Nat.Primes,
        ((Real.log p / (μ p).real {g : ℚ_[p] | ‖g‖ = 1} : ℝ) : ℂ) *
          ∫ g in {g : ℚ_[p] | g ≠ 0},
            φ ‖g‖ * ((‖g‖ ^ (1/2 : ℝ) / ‖1 - g‖ * (1 / ‖g‖) : ℝ) : ℂ) ∂(μ p) =
      mellin φ (1 / 2) + mellin φ (-1 / 2) -
        ∑' ρ : ZetaZerosInTraceStrip α, zetaTraceTerm φ α ρ := by
  obtain ⟨hi, hp, _hfinite, hsum, _hpp, hgeo⟩ :=
    MasulloAudit.geometric_side_eq_formal_lhs φ hφ inst μ
  obtain ⟨_hi, _hp, hz, heq⟩ :=
    trace_formula_of_inversion_even MasulloRH.trace_formula_inversion_even α hα φ hφ
  exact ⟨hi, hp, hsum, hz, hgeo.trans heq⟩

end

-- Step 7: `MasulloAudit.trace_formula_rational_source_form` implies `MasulloRH.trace_formula_rational` (accepted reduction of `MasulloRH.trace_formula_rational`).
section

set_option autoImplicit false

open MeasureTheory Set MasulloRH
open scoped Topology

namespace LinkTfrSourceForm

/-- The combined real-place integrand is integrable on `(1, ∞)`: it vanishes for large `t`, and
near `1` the zero `ϕ(1) = 0` cancels the simple pole of `√t/(t²-1)` (Lipschitz bound). -/

theorem integrableOn_realTraceIntegrand' (φ : ℝ → ℂ) (hφ : IsRationalTraceTest φ) :
    IntegrableOn (realTraceIntegrand φ) (Ioi 1) := by
  obtain ⟨hsm, hcs, hts, h1⟩ := hφ
  have hK : IsCompact (tsupport φ) := hcs
  -- bounds a, b of the support
  obtain ⟨a, ha0, hab⟩ : ∃ a > 0, ∀ x ∈ tsupport φ, a ≤ x := by
    rcases (tsupport φ).eq_empty_or_nonempty with h | h
    · exact ⟨1, one_pos, by simp [h]⟩
    · obtain ⟨x0, hx0, hmin⟩ := hK.exists_isMinOn h continuous_id.continuousOn
      exact ⟨x0, hts hx0, fun x hx => hmin hx⟩
  obtain ⟨b, hb⟩ : ∃ b, ∀ x ∈ tsupport φ, x ≤ b := hK.bddAbove
  set R : ℝ := max (max b (1 / a)) 2 with hR
  have hR2 : 2 ≤ R := le_max_right _ _
  have hRb : b ≤ R := (le_max_left _ _).trans (le_max_left _ _)
  have hRa : 1 / a ≤ R := (le_max_right _ _).trans (le_max_left _ _)
  have hzero : ∀ x, φ x ≠ 0 → x ∈ tsupport φ := fun x hx => subset_tsupport _ hx
  -- vanishing beyond R
  have hvan : ∀ t, R < t → realTraceIntegrand φ t = 0 := by
    intro t ht
    have ht0 : 0 < t := by linarith
    have e1 : φ t = 0 := by
      by_contra h; have := hb t (hzero t h); linarith
    have e2 : φ t⁻¹ = 0 := by
      by_contra h
      have := hab _ (hzero _ h)
      have hlt : t⁻¹ < a := by
        rw [inv_lt_comm₀ ht0 ha0]; rw [one_div] at hRa; linarith
      linarith
    simp [realTraceIntegrand, e1, e2]
  -- g = φ + φ ∘ inv is Lipschitz on [1, R]
  set g : ℝ → ℂ := fun t => φ t + φ t⁻¹ with hg
  have hgc : ContDiffOn ℝ 1 g (Icc 1 R) := by
    have h1' : ContDiff ℝ 1 φ := hsm.of_le (by exact_mod_cast le_top)
    refine h1'.contDiffOn.add ?_
    refine h1'.comp_contDiffOn ?_
    exact (contDiffOn_inv ℝ).mono (fun x hx => by
      simp only [mem_compl_iff, mem_singleton_iff]; linarith [hx.1])
  obtain ⟨L, hL⟩ := hgc.exists_lipschitzOnWith one_ne_zero (convex_Icc 1 R) isCompact_Icc
  have hg1 : g 1 = 0 := by simp [hg, h1]
  have hbound : ∀ t ∈ Ioc (1:ℝ) R, ‖realTraceIntegrand φ t‖ ≤ L := by
    intro t ht
    have hdist := hL.dist_le_mul t ⟨ht.1.le, ht.2⟩ 1 ⟨le_rfl, by linarith⟩
    rw [dist_eq_norm, hg1, sub_zero, Real.dist_eq, abs_of_pos (by linarith [ht.1])] at hdist
    have ht1 : 0 < t - 1 := by linarith [ht.1]
    have hden : 0 < t ^ 2 - 1 := by nlinarith [ht.1]
    have hsq : Real.sqrt t ≤ t + 1 := by
      rw [Real.sqrt_le_left (by linarith)]; nlinarith [ht.1]
    rw [realTraceIntegrand, norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (div_nonneg (Real.sqrt_nonneg _) hden.le)]
    calc ‖g t‖ * (Real.sqrt t / (t ^ 2 - 1))
        ≤ (L * (t - 1)) * (Real.sqrt t / (t ^ 2 - 1)) :=
          mul_le_mul_of_nonneg_right hdist (div_nonneg (Real.sqrt_nonneg _) hden.le)
      _ = L * ((t - 1) * Real.sqrt t / (t ^ 2 - 1)) := by ring
      _ ≤ L * 1 := by
          apply mul_le_mul_of_nonneg_left _ L.2
          rw [div_le_one hden]
          nlinarith [Real.sqrt_nonneg t]
      _ = L := mul_one _
  have hmeas : AEStronglyMeasurable (realTraceIntegrand φ) (volume.restrict (Ioi 1)) := by
    apply ContinuousOn.aestronglyMeasurable _ measurableSet_Ioi
    intro t ht
    have ht0 : (t:ℝ) ≠ 0 := by have := ht.out; linarith
    have hne : t ^ 2 - 1 ≠ 0 := by have := ht.out; nlinarith
    apply ContinuousAt.continuousWithinAt
    unfold realTraceIntegrand
    refine ContinuousAt.mul ?_ ?_
    · exact (hsm.continuous.continuousAt).add
        ((hsm.continuous.continuousAt).comp (continuousAt_inv₀ ht0))
    · refine Complex.continuous_ofReal.continuousAt.comp ?_
      exact (Real.continuous_sqrt.continuousAt).div (by fun_prop) hne
  have hsub : Ioi (1:ℝ) ⊆ Ioc 1 R ∪ Ioi R := fun t ht => by
    rcases le_or_gt t R with h | h
    · exact Or.inl ⟨ht, h⟩
    · exact Or.inr h
  refine IntegrableOn.mono_set (IntegrableOn.union ?_ ?_) hsub
  · refine ⟨hmeas.mono_set Ioc_subset_Ioi_self,
      .restrict_of_bounded (C := (L:ℝ)) measure_Ioc_lt_top ?_⟩
    rw [ae_restrict_iff' measurableSet_Ioc]
    exact Filter.Eventually.of_forall hbound
  · exact (integrableOn_zero).congr_fun (fun t ht => (hvan t ht).symm) measurableSet_Ioi

end LinkTfrSourceForm

open LinkTfrSourceForm in
theorem MasulloRH.trace_formula_rational (α : ℝ) (hα : 0 < α) (φ : ℝ → ℂ)
    (hφ : IsRationalTraceTest φ) :
    IntegrableOn (realTraceIntegrand φ) (Ioi 1) ∧
    Summable (primePowerTraceTerm φ) ∧
    Summable (zetaTraceTerm φ α) ∧
    (∫ t in Ioi (1 : ℝ), realTraceIntegrand φ t) +
      (∑' i : Nat.Primes × ℕ, primePowerTraceTerm φ i) =
      mellin φ (1 / 2) + mellin φ (-1 / 2) -
        ∑' ρ : ZetaZerosInTraceStrip α, zetaTraceTerm φ α ρ := by
  have : ∀ p : Nat.Primes, Fact (p : ℕ).Prime := fun p => ⟨p.2⟩
  let inst : ∀ p : Nat.Primes, MeasurableSpace ℚ_[p] := fun p => borel ℚ_[p]
  have hB : ∀ p : Nat.Primes, BorelSpace ℚ_[p] := fun p => ⟨rfl⟩
  let μ : ∀ p : Nat.Primes, Measure ℚ_[p] := fun p => Measure.addHaar
  have hμ : ∀ p : Nat.Primes, (μ p).IsAddHaarMeasure := fun p => by
    dsimp only [μ]; infer_instance
  obtain ⟨-, -, -, -, hpp, hgeom⟩ :=
    MasulloAudit.geometric_side_eq_formal_lhs φ hφ inst μ
  obtain ⟨-, -, -, hz, hsrc⟩ :=
    MasulloAudit.trace_formula_rational_source_form α hα φ hφ inst μ
  refine ⟨integrableOn_realTraceIntegrand' φ hφ, hpp, hz, ?_⟩
  rw [← hgeom]
  exact hsrc

end

-- Step 8: `MasulloRH.trace_formula_rational` implies `RiemannHypothesis` (accepted reduction of `mathlib_riemannHypothesis`).
section

theorem solution : RiemannHypothesis :=
  MasulloRH.trace_formula_rational_iff_RH.mp
    (fun α hα φ hφ => MasulloRH.trace_formula_rational α hα φ hφ)

end
