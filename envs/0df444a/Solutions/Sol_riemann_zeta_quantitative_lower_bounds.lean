-- Prove2me | solution 1 for riemann_zeta_quantitative_lower_bounds
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T07:19:25.667606+00:00
-- url     : https://prove2.me/submissions/816b6326-4cec-4d4a-8d67-a38c46ce76f2

import Mathlib.NumberTheory.LSeries.Dirichlet
import Mathlib.NumberTheory.LSeries.Nonvanishing
import Mathlib.Analysis.Analytic.Uniqueness
import Mathlib.Analysis.Complex.Convex
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Mathlib.NumberTheory.LSeries.SumCoeff
import Mathlib.Analysis.MellinTransform
open MeasureTheory
open scoped Topology

set_option autoImplicit false

open Complex Filter MeasureTheory Asymptotics
open scoped Topology

namespace ZetaLower4ad.Mertens
open Set

noncomputable def summatoryReal (f : ℕ → ℂ) (t : ℝ) : ℂ :=
  ∑ k ∈ Finset.Icc 1 ⌊t⌋₊, f k

noncomputable def mellinExtension (f : ℕ → ℂ) (s : ℂ) : ℂ :=
  s * mellin (summatoryReal f) (-s)

lemma summatoryReal_eq_zero {f : ℕ → ℂ} {t : ℝ} (ht : t < 1) :
    summatoryReal f t = 0 := by
  simp [summatoryReal, Nat.floor_eq_zero.mpr ht]

lemma locallyIntegrableOn_summatoryReal (f : ℕ → ℂ) :
    LocallyIntegrableOn (summatoryReal f) (Ioi 0) := by
  have hconstant : LocallyIntegrableOn (fun _ : ℝ => (1 : ℂ)) (Ici 0) :=
    continuous_const.continuousOn.locallyIntegrableOn measurableSet_Ici
  have hstep := locallyIntegrableOn_mul_sum_Icc f (m := 1) (a := 0) le_rfl hconstant
  have hstep' : LocallyIntegrableOn (summatoryReal f) (Ici 0) := by
    change LocallyIntegrableOn (fun t : ℝ => ∑ k ∈ Finset.Icc 1 ⌊t⌋₊, f k) (Ici 0)
    simpa only [one_mul] using hstep
  exact hstep'.mono_set Ioi_subset_Ici_self

lemma summatoryReal_isBigO_atTop {f : ℕ → ℂ} {r : ℝ} (hr : 0 ≤ r)
    (hO : (fun n : ℕ => ∑ k ∈ Finset.Icc 1 n, f k) =O[atTop]
      (fun n : ℕ => (n : ℝ) ^ r)) :
    summatoryReal f =O[atTop] (fun t : ℝ => t ^ r) := by
  exact (hO.comp_tendsto tendsto_nat_floor_atTop).trans
    (isEquivalent_nat_floor.isBigO.rpow hr (eventually_ge_atTop 0))

lemma summatoryReal_isBigO_atZero (f : ℕ → ℂ) (b : ℝ) :
    summatoryReal f =O[𝓝[>] 0] (fun t : ℝ => t ^ (-b)) := by
  have heq : (fun _ : ℝ => (0 : ℂ)) =ᶠ[𝓝[>] 0] summatoryReal f := by
    filter_upwards [(eventually_lt_nhds (show (0 : ℝ) < 1 by norm_num)).filter_mono
      nhdsWithin_le_nhds] with t ht
    exact (summatoryReal_eq_zero ht).symm
  exact (isBigO_zero (fun t : ℝ => t ^ (-b)) (𝓝[>] 0)).congr' heq Filter.EventuallyEq.rfl

theorem differentiableAt_mellinExtension_of_partialSums
    {f : ℕ → ℂ} {r : ℝ} (hr : 0 ≤ r)
    (hO : (fun n : ℕ => ∑ k ∈ Finset.Icc 1 n, f k) =O[atTop]
      (fun n : ℕ => (n : ℝ) ^ r))
    {s : ℂ} (hs : r < s.re) :
    DifferentiableAt ℂ (mellinExtension f) s := by
  have htop : summatoryReal f =O[atTop] (fun t : ℝ => t ^ (-(-r))) := by
    simpa using summatoryReal_isBigO_atTop hr hO
  have hd : DifferentiableAt ℂ (mellin (summatoryReal f)) (-s) :=
    mellin_differentiableAt_of_isBigO_rpow (locallyIntegrableOn_summatoryReal f)
      htop (by simp only [neg_re]; linarith)
      (summatoryReal_isBigO_atZero f (-s.re - 1)) (by simp only [neg_re]; linarith)
  exact differentiableAt_id.mul (hd.comp s differentiableAt_id.neg)

theorem mellin_summatoryReal_neg_eq_integral (f : ℕ → ℂ) (s : ℂ) :
    mellin (summatoryReal f) (-s) =
      ∫ t in Set.Ioi (1 : ℝ), summatoryReal f t * (t : ℂ) ^ (-(s + 1)) := by
  rw [mellin]
  have hcut :
      (∫ t in Set.Ioi (0 : ℝ), (t : ℂ) ^ (-s - 1) • summatoryReal f t) =
      ∫ t in Set.Ici (1 : ℝ), (t : ℂ) ^ (-s - 1) • summatoryReal f t := by
    apply setIntegral_eq_of_subset_of_forall_sdiff_eq_zero measurableSet_Ioi
    · intro t ht
      exact lt_of_lt_of_le (show (0 : ℝ) < 1 by norm_num) ht
    · intro t ht
      have ht1 : t < 1 := lt_of_not_ge ht.2
      rw [summatoryReal_eq_zero ht1, smul_zero]
  rw [hcut, integral_Ici_eq_integral_Ioi]
  apply setIntegral_congr_fun measurableSet_Ioi
  intro t ht
  dsimp only
  rw [smul_eq_mul, show -s - 1 = -(s + 1) by ring, mul_comm]

theorem mellinExtension_eq_LSeries (f : ℕ → ℂ) {r : ℝ} (hr : 0 ≤ r)
    {s : ℂ} (hs : r < s.re) (hS : LSeriesSummable f s)
    (hO : (fun n : ℕ => ∑ k ∈ Finset.Icc 1 n, f k) =O[atTop]
      fun n => (n : ℝ) ^ r) :
    mellinExtension f s = LSeries f s := by
  rw [mellinExtension, mellin_summatoryReal_neg_eq_integral]
  exact (LSeries_eq_mul_integral f hr hs hS hO).symm

end ZetaLower4ad.Mertens

namespace ZetaLower4ad.Mertens
open Finset

theorem norm_mellin_tail_le
    (M : ℝ → ℂ) {r C a : ℝ} (ha : 0 < a) {s : ℂ} (hs : r < s.re)
    (hM : ∀ t : ℝ, a < t → ‖M t‖ ≤ C * t ^ r) :
    ‖s * ∫ t in Set.Ioi a, M t * (t : ℂ) ^ (-(s + 1))‖ ≤
      C * ‖s‖ / (s.re - r) * a ^ (r - s.re) := by
  have hexp : r - s.re - 1 < -1 := by linarith
  have hbound : ∀ᵐ t : ℝ ∂volume.restrict (Set.Ioi a),
      ‖M t * (t : ℂ) ^ (-(s + 1))‖ ≤ C * t ^ (r - s.re - 1) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    have ht0 : 0 < t := ha.trans ht
    rw [norm_mul, norm_cpow_eq_rpow_re_of_pos ht0, neg_re, add_re, one_re]
    calc
      ‖M t‖ * t ^ (-(s.re + 1)) ≤ (C * t ^ r) * t ^ (-(s.re + 1)) :=
        mul_le_mul_of_nonneg_right (hM t ht) (Real.rpow_nonneg ht0.le _)
      _ = C * t ^ (r - s.re - 1) := by
        rw [mul_assoc, ← Real.rpow_add ht0]
        congr 2
        ring
  have hnorm := norm_integral_le_of_norm_le
    ((integrableOn_Ioi_rpow_of_lt hexp ha).const_mul C) hbound
  rw [integral_const_mul, integral_Ioi_rpow_of_lt hexp ha] at hnorm
  rw [norm_mul]
  refine (mul_le_mul_of_nonneg_left hnorm (norm_nonneg s)).trans_eq ?_
  rw [show r - s.re - 1 + 1 = r - s.re by ring]
  have hden : s.re - r ≠ 0 := (sub_pos.mpr hs).ne'
  have hden' : r - s.re ≠ 0 := (sub_neg.mpr hs).ne
  field_simp [hden, hden']
  ring

theorem summatoryReal_norm_le (f : ℕ → ℂ) {r C : ℝ} (hr : 0 ≤ r) (hC : 0 ≤ C)
    (hbound : ∀ n : ℕ, 1 ≤ n → ‖∑ k ∈ Icc 1 n, f k‖ ≤ C * (n : ℝ) ^ r)
    {t : ℝ} (ht : 1 ≤ t) :
    ‖summatoryReal f t‖ ≤ C * t ^ r := by
  have hfloor : 1 ≤ ⌊t⌋₊ := (Nat.one_le_floor_iff t).mpr ht
  calc
    ‖summatoryReal f t‖ ≤ C * (⌊t⌋₊ : ℝ) ^ r := hbound _ hfloor
    _ ≤ C * t ^ r := mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow (Nat.cast_nonneg _) (Nat.floor_le (zero_le_one.trans ht)) hr) hC

end ZetaLower4ad.Mertens

namespace ZetaLower4ad.Regularization

noncomputable def regularizedZeta (s : ℂ) : ℂ :=
  (s * (1 - s) * completedRiemannZeta₀ s - 1) * (Gammaℝ s)⁻¹

lemma differentiable_regularizedZeta : Differentiable ℂ regularizedZeta := by
  exact (((differentiable_id.mul (differentiable_const 1 |>.sub differentiable_id)).mul
    differentiable_completedZeta₀).sub (differentiable_const 1)).mul
      differentiable_Gammaℝ_inv

lemma regularizedZeta_eq {s : ℂ} (hs0 : s ≠ 0) (hs1 : s ≠ 1) :
    regularizedZeta s = s * (1 - s) * riemannZeta s := by
  rw [regularizedZeta, riemannZeta_def_of_ne_zero hs0, completedRiemannZeta_eq]
  have h1s : 1 - s ≠ 0 := sub_ne_zero.mpr (Ne.symm hs1)
  field_simp
  ring

end ZetaLower4ad.Regularization

namespace ZetaLower4ad.Bounds
open Set

theorem zeta_mul_moebius_extension_eq_one
    {r : ℝ} (hr : 0 ≤ r) (hr1 : r < 1)
    (F : ℂ → ℂ)
    (hF : DifferentiableOn ℂ F {s : ℂ | r < s.re})
    (hmatch : ∀ s : ℂ, 1 < s.re →
      F s = LSeries (fun n : ℕ => (ArithmeticFunction.moebius n : ℂ)) s)
    {s : ℂ} (hs : r < s.re) (hs1 : s ≠ 1) :
    riemannZeta s * F s = 1 := by
  let H : Set ℂ := {z : ℂ | r < z.re}
  have hopen : IsOpen H := isOpen_lt continuous_const Complex.continuous_re
  have hleft : AnalyticOnNhd ℂ (fun z => ZetaLower4ad.Regularization.regularizedZeta z * F z) H :=
    (ZetaLower4ad.Regularization.differentiable_regularizedZeta.differentiableOn.mul hF).analyticOnNhd hopen
  have hpoly : Differentiable ℂ (fun z : ℂ => z * (1 - z)) :=
    differentiable_id.mul ((differentiable_const (1 : ℂ)).sub differentiable_id)
  have hright : AnalyticOnNhd ℂ (fun z : ℂ => z * (1 - z)) H :=
    hpoly.differentiableOn.analyticOnNhd hopen
  have hmatch' : (fun z => ZetaLower4ad.Regularization.regularizedZeta z * F z) =ᶠ[𝓝 (2 : ℂ)]
      (fun z => z * (1 - z)) := by
    have hn : {z : ℂ | 1 < z.re} ∈ 𝓝 (2 : ℂ) :=
      (isOpen_lt continuous_const Complex.continuous_re).mem_nhds (by norm_num)
    filter_upwards [hn] with z hz
    have hz0 : z ≠ 0 := ne_zero_of_re_pos (by linarith)
    have hz1 : z ≠ 1 := by
      intro h
      subst z
      norm_num at hz
    rw [ZetaLower4ad.Regularization.regularizedZeta_eq hz0 hz1, hmatch z hz, mul_assoc]
    have hi := LSeries_one_mul_Lseries_moebius hz
    rw [LSeries_one_eq_riemannZeta hz] at hi
    rw [hi, mul_one]
  have htwo : (2 : ℂ) ∈ H := by
    norm_num [H]
    linarith
  have heq : EqOn (fun z => ZetaLower4ad.Regularization.regularizedZeta z * F z)
      (fun z => z * (1 - z)) H :=
    hleft.eqOn_of_preconnected_of_eventuallyEq hright
      (convex_halfSpace_re_gt r).isPreconnected htwo hmatch'
  have hs0 : s ≠ 0 := ne_zero_of_re_pos (hr.trans_lt hs)
  have hpoly0 : s * (1 - s) ≠ 0 :=
    mul_ne_zero hs0 (sub_ne_zero.mpr (Ne.symm hs1))
  have hid := heq hs
  dsimp only at hid
  rw [ZetaLower4ad.Regularization.regularizedZeta_eq hs0 hs1] at hid
  apply mul_left_cancel₀ hpoly0
  simpa only [mul_assoc, mul_one] using hid

theorem zeta_mul_mellinExtension_eq_one_of_mertens_power_bound
    {r : ℝ} (hr : 0 ≤ r)
    (hM : (fun N : ℕ => ∑ n ∈ Finset.Icc 1 N,
      (ArithmeticFunction.moebius n : ℂ)) =O[atTop]
      (fun N : ℕ => (N : ℝ) ^ r))
    {s : ℂ} (hs : r < s.re) (hs1 : s ≠ 1) :
    riemannZeta s * ZetaLower4ad.Mertens.mellinExtension
      (fun n => (ArithmeticFunction.moebius n : ℂ)) s = 1 := by
  by_cases hr1 : r < 1
  · apply zeta_mul_moebius_extension_eq_one hr hr1
      (ZetaLower4ad.Mertens.mellinExtension (fun n => (ArithmeticFunction.moebius n : ℂ)))
      ?_ ?_ hs hs1
    · intro z hz
      exact (ZetaLower4ad.Mertens.differentiableAt_mellinExtension_of_partialSums hr hM
        hz).differentiableWithinAt
    · intro z hz
      exact ZetaLower4ad.Mertens.mellinExtension_eq_LSeries _ hr (hr1.trans hz)
        (ArithmeticFunction.LSeriesSummable_moebius_iff.mpr hz) hM
  · have hsre : 1 < s.re := by linarith
    rw [ZetaLower4ad.Mertens.mellinExtension_eq_LSeries _ hr hs
      (ArithmeticFunction.LSeriesSummable_moebius_iff.mpr hsre) hM]
    have hprod := LSeries_one_mul_Lseries_moebius hsre
    rwa [LSeries_one_eq_riemannZeta hsre] at hprod

theorem norm_mellinExtension_le_of_partialSums_bound
    (f : ℕ → ℂ) {r C : ℝ} (hr : 0 ≤ r) (hC : 0 ≤ C)
    (hbound : ∀ N : ℕ, 1 ≤ N →
      ‖∑ n ∈ Finset.Icc 1 N, f n‖ ≤ C * (N : ℝ) ^ r)
    {s : ℂ} (hs : r < s.re) :
    ‖ZetaLower4ad.Mertens.mellinExtension f s‖ ≤ C * ‖s‖ / (s.re - r) := by
  have htail := ZetaLower4ad.Mertens.norm_mellin_tail_le (ZetaLower4ad.Mertens.summatoryReal f)
    (by norm_num : (0 : ℝ) < 1) hs
    (fun t ht => ZetaLower4ad.Mertens.summatoryReal_norm_le f hr hC hbound ht.le)
  simpa only [ZetaLower4ad.Mertens.mellinExtension, ZetaLower4ad.Mertens.mellin_summatoryReal_neg_eq_integral,
    Real.one_rpow, mul_one] using htail

theorem riemannZeta_norm_lower_bound_of_mertens_bound
    {r C : ℝ} (hr : 0 ≤ r) (hC : 0 < C)
    (hbound : ∀ N : ℕ, 1 ≤ N →
      ‖∑ n ∈ Finset.Icc 1 N, (ArithmeticFunction.moebius n : ℂ)‖ ≤
        C * (N : ℝ) ^ r)
    {s : ℂ} (hs : r < s.re) (hs1 : s ≠ 1) :
    (s.re - r) / (C * ‖s‖) ≤ ‖riemannZeta s‖ := by
  have hM : (fun N : ℕ => ∑ n ∈ Finset.Icc 1 N,
      (ArithmeticFunction.moebius n : ℂ)) =O[atTop]
      (fun N : ℕ => (N : ℝ) ^ r) := by
    refine IsBigO.of_bound C ?_
    filter_upwards [eventually_ge_atTop 1] with N hN
    simpa only [Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg (Nat.cast_nonneg N) r)]
      using hbound N hN
  have hprod := zeta_mul_mellinExtension_eq_one_of_mertens_power_bound hr hM hs hs1
  have hnormprod : ‖riemannZeta s‖ *
      ‖ZetaLower4ad.Mertens.mellinExtension (fun n => (ArithmeticFunction.moebius n : ℂ)) s‖ = 1 := by
    simpa only [norm_mul, norm_one] using congrArg norm hprod
  have hFbound := norm_mellinExtension_le_of_partialSums_bound
    (fun n => (ArithmeticFunction.moebius n : ℂ)) hr hC.le hbound hs
  have hsmall : 1 ≤ ‖riemannZeta s‖ * (C * ‖s‖ / (s.re - r)) := by
    rw [← hnormprod]
    exact mul_le_mul_of_nonneg_left hFbound (norm_nonneg _)
  have hs0 : s ≠ 0 := ne_zero_of_re_pos (hr.trans_lt hs)
  apply (div_le_iff₀ (mul_pos hC (norm_pos_iff.mpr hs0))).mpr
  rw [← mul_div_assoc] at hsmall
  simpa only [one_mul] using (le_div_iff₀ (sub_pos.mpr hs)).mp hsmall

end ZetaLower4ad.Bounds

open Complex Filter Set Asymptotics
open scoped Topology ComplexOrder

namespace ZetaLower4ad.Bounds

lemma norm_LSeries_le_real_zeta_of_norm_le_one
    (f : ℕ → ℂ) (hf : ∀ n : ℕ, ‖f n‖ ≤ 1) {s : ℂ} (hs : 1 < s.re) :
    ‖LSeries f s‖ ≤ ‖riemannZeta (s.re : ℂ)‖ := by
  have hsreal : 1 < (s.re : ℂ).re := by simpa using hs
  have hS : LSeriesSummable 1 (s.re : ℂ) := LSeriesSummable_one_iff.mpr hsreal
  have hre : HasSum (fun n : ℕ => (LSeries.term 1 (s.re : ℂ) n).re)
      (LSeries 1 (s.re : ℂ)).re := Complex.hasSum_re hS.hasSum
  have hnorm : ∀ n : ℕ, ‖LSeries.term f s n‖ ≤ (LSeries.term 1 (s.re : ℂ) n).re := by
    intro n
    have hnonneg : 0 ≤ LSeries.term 1 (s.re : ℂ) n :=
      LSeries.term_nonneg (by simp) s.re
    rw [Complex.re_eq_norm.mpr hnonneg]
    calc
      ‖LSeries.term f s n‖ ≤ ‖LSeries.term 1 s n‖ :=
        LSeries.norm_term_le s (by simpa using hf n)
      _ = ‖LSeries.term 1 (s.re : ℂ) n‖ := by
        simp only [LSeries.norm_term_eq, ofReal_re]
  have hmajor := tsum_of_norm_bounded hre hnorm
  change ‖LSeries f s‖ ≤ (LSeries 1 (s.re : ℂ)).re at hmajor
  rw [LSeries_one_eq_riemannZeta hsreal] at hmajor
  exact hmajor.trans (Complex.re_le_norm _)

lemma real_riemannZeta_norm_le {σ : ℝ} (hσ : 1 < σ) :
    ‖riemannZeta (σ : ℂ)‖ ≤ σ / (σ - 1) := by
  have hbound : ∀ N : ℕ, 1 ≤ N →
      ‖∑ n ∈ Finset.Icc 1 N, (1 : ℕ → ℂ) n‖ ≤ (1 : ℝ) * (N : ℝ) ^ (1 : ℝ) := by
    intro N hN
    simp
  have hO : (fun N : ℕ => ∑ n ∈ Finset.Icc 1 N, (1 : ℕ → ℂ) n) =O[atTop]
      (fun N : ℕ => (N : ℝ) ^ (1 : ℝ)) := by
    refine IsBigO.of_bound 1 ?_
    filter_upwards [eventually_ge_atTop 1] with N hN
    simpa only [Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg (Nat.cast_nonneg N) 1)]
      using hbound N hN
  have hσreal : 1 < (σ : ℂ).re := by simpa using hσ
  have hnorm := norm_mellinExtension_le_of_partialSums_bound (1 : ℕ → ℂ)
    (by norm_num : (0 : ℝ) ≤ 1) (by norm_num : (0 : ℝ) ≤ 1) hbound hσreal
  rw [ZetaLower4ad.Mertens.mellinExtension_eq_LSeries _ (by norm_num) hσreal
    (LSeriesSummable_one_iff.mpr hσreal) hO,
    LSeries_one_eq_riemannZeta hσreal] at hnorm
  simpa only [one_mul, ofReal_re, norm_real, Real.norm_eq_abs,
    abs_of_pos (zero_lt_one.trans hσ)] using hnorm

/-- A uniform lower bound on every vertical line strictly to the right of one. -/
theorem riemannZeta_norm_lower_bound_real_part
    {s : ℂ} (hs : 1 < s.re) :
    (s.re - 1) / s.re ≤ ‖riemannZeta s‖ := by
  have hmu : ‖LSeries (fun n : ℕ => (ArithmeticFunction.moebius n : ℂ)) s‖ ≤
      s.re / (s.re - 1) := by
    refine (norm_LSeries_le_real_zeta_of_norm_le_one _ ?_ hs).trans (real_riemannZeta_norm_le hs)
    intro n
    rw [Complex.norm_intCast]
    exact_mod_cast (ArithmeticFunction.abs_moebius_le_one (n := n))
  have hprod := LSeries_one_mul_Lseries_moebius hs
  rw [LSeries_one_eq_riemannZeta hs] at hprod
  have hnormprod : ‖riemannZeta s‖ *
      ‖LSeries (fun n : ℕ => (ArithmeticFunction.moebius n : ℂ)) s‖ = 1 := by
    simpa only [norm_mul, norm_one] using congrArg norm hprod
  have hsmall : 1 ≤ ‖riemannZeta s‖ * (s.re / (s.re - 1)) := by
    nth_rw 1 [← hnormprod]
    exact mul_le_mul_of_nonneg_left hmu (norm_nonneg _)
  apply (div_le_iff₀ (zero_lt_one.trans hs)).mpr
  rw [← mul_div_assoc] at hsmall
  simpa only [one_mul] using (le_div_iff₀ (sub_pos.mpr hs)).mp hsmall

end ZetaLower4ad.Bounds

theorem solution :
    (∀ (r C : ℝ), 0 ≤ r → 0 < C →
      (∀ N : ℕ, 1 ≤ N →
        ‖∑ n ∈ Finset.Icc 1 N, (ArithmeticFunction.moebius n : ℂ)‖ ≤
          C * (N : ℝ) ^ r) →
      ∀ s : ℂ, r < s.re → s ≠ 1 →
        (s.re - r) / (C * ‖s‖) ≤ ‖riemannZeta s‖) ∧
    (∀ s : ℂ, 1 < s.re → (s.re - 1) / s.re ≤ ‖riemannZeta s‖) := by
  constructor
  · intro r C hr hC hbound s hs hs1
    exact ZetaLower4ad.Bounds.riemannZeta_norm_lower_bound_of_mertens_bound hr hC hbound hs hs1
  · intro s hs
    exact ZetaLower4ad.Bounds.riemannZeta_norm_lower_bound_real_part hs

#print axioms solution
