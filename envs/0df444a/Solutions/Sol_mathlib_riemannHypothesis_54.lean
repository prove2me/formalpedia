-- Prove2me | solution 54 for mathlib_riemannHypothesis
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T22:30:14.84412+00:00
-- url     : https://prove2.me/submissions/e3e9e2b9-ac07-40e7-84dc-2450350cfa9e
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Theorems.Thm_MasulloRH_trace_formula_inversion_even
import Theorems.Thm_MasulloAudit_geometric_side_eq_formal_lhs
import Theorems.Thm_MasulloRH_trace_formula_inversion_odd
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Tactic.Ring
import Mathlib.Tactic.LinearCombination
import Mathlib.NumberTheory.Padics.ProperSpace
import Mathlib.MeasureTheory.Measure.Haar.Basic
import Mathlib.Analysis.Calculus.ContDiff.RCLike
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Theorems.Thm_MasulloRH_trace_formula_rational_iff_RH

-- Step 1: `MasulloRH.trace_formula_inversion_even` implies `MasulloAudit.trace_formula_rational_source_form` (accepted reduction of `MasulloAudit.trace_formula_rational_source_form`).
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

-- Step 2: `MasulloAudit.trace_formula_rational_source_form` implies `MasulloRH.trace_formula_rational` (accepted reduction of `MasulloRH.trace_formula_rational`).
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

-- Step 3: `MasulloRH.trace_formula_rational` implies `RiemannHypothesis` (accepted reduction of `mathlib_riemannHypothesis`).
section

theorem solution : RiemannHypothesis :=
  MasulloRH.trace_formula_rational_iff_RH.mp
    (fun α hα φ hφ => MasulloRH.trace_formula_rational α hα φ hφ)

end
