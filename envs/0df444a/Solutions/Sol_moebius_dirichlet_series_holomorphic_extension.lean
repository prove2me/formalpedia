-- Prove2me | solution 1 for moebius_dirichlet_series_holomorphic_extension
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T02:34:52.900654+00:00
-- url     : https://prove2.me/submissions/81e4ee1d-f697-40c6-bac3-608ebcef77cf
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Theorems.Thm_moebius_summatory_rpow_bound
import Mathlib.Analysis.MellinTransform
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

open Complex Filter Set MeasureTheory Asymptotics
open scoped Topology

namespace RHMertens

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

theorem differentiableOn_mellinExtension_of_mertens
    {f : ℕ → ℂ}
    (hO : ∀ ε : ℝ, 0 < ε →
      (fun n : ℕ => ∑ k ∈ Finset.Icc 1 n, f k) =O[atTop]
      (fun n : ℕ => (n : ℝ) ^ (1 / 2 + ε))) :
    DifferentiableOn ℂ (mellinExtension f) {s : ℂ | 1 / 2 < s.re} := by
  intro s hs
  have heps : 0 < (s.re - 1 / 2) / 2 := by
    change 1 / 2 < s.re at hs
    linarith
  exact (differentiableAt_mellinExtension_of_partialSums
    (by linarith : 0 ≤ 1 / 2 + (s.re - 1 / 2) / 2)
    (hO _ heps) (by change 1 / 2 < s.re at hs; linarith)).differentiableWithinAt

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

theorem mellinExtension_moebius_eq
    (hMertens : ∀ ε : ℝ, 0 < ε →
      (fun n : ℕ => ∑ k ∈ Finset.Icc 1 n, (ArithmeticFunction.moebius k : ℂ)) =O[atTop]
      fun n => (n : ℝ) ^ (1 / 2 + ε))
    {s : ℂ} (hs : 1 < s.re) :
    mellinExtension (fun n => (ArithmeticFunction.moebius n : ℂ)) s =
      LSeries (fun n => (ArithmeticFunction.moebius n : ℂ)) s := by
  apply mellinExtension_eq_LSeries (r := 1 / 2 + 1 / 4)
  · norm_num
  · linarith
  · exact ArithmeticFunction.LSeriesSummable_moebius_iff.mpr hs
  · exact hMertens (1 / 4) (by norm_num)

theorem extension_of_mertens
    (hMertens : ∀ ε : ℝ, 0 < ε →
      (fun N : ℕ => ∑ n ∈ Finset.Icc 1 N, (ArithmeticFunction.moebius n : ℂ)) =O[atTop]
        (fun N : ℕ => (N : ℝ) ^ (1 / 2 + ε))) :
    ∃ F : ℂ → ℂ,
      DifferentiableOn ℂ F {s : ℂ | 1 / 2 < s.re} ∧
      ∀ s : ℂ, 1 < s.re →
        F s = LSeries (fun n : ℕ => (ArithmeticFunction.moebius n : ℂ)) s := by
  refine ⟨mellinExtension (fun n => (ArithmeticFunction.moebius n : ℂ)),
    differentiableOn_mellinExtension_of_mertens hMertens, ?_⟩
  exact fun _ hs => mellinExtension_moebius_eq hMertens hs

end RHMertens

-- Only the imported arithmetic growth estimate remains open.
theorem solution :
    ∃ F : ℂ → ℂ,
      DifferentiableOn ℂ F {s : ℂ | 1 / 2 < s.re} ∧
      ∀ s : ℂ, 1 < s.re →
        F s = LSeries (fun n : ℕ => (ArithmeticFunction.moebius n : ℂ)) s := by
  exact RHMertens.extension_of_mertens moebius_summatory_rpow_bound
