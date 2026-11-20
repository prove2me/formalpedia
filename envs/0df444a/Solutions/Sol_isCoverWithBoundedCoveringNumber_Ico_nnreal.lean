-- Prove2me | solution 1 for isCoverWithBoundedCoveringNumber_Ico_nnreal
-- status  : ACCEPTED   (prove)
-- author  : @martelus trismortuus
-- created : 2026-11-19T14:48:53.01842+00:00
-- url     : https://prove2.me/submissions/a8fd7ae0-f258-49cb-b573-9e50e3beeb6c

import Definitions.Def_BrownianMotion_Continuity_HasBoundedInternalCoveringNumber_F001
import Definitions.Def_BrownianMotion_Continuity_CoveringNumber_F001

/-
Copyright (c) 2025 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/

/-!
# HasBoundedCoveringNumber

-/

@[expose] public section

open MeasureTheory Metric
open scoped ENNReal NNReal

variable {T : Type*} [PseudoEMetricSpace T] {A : Set T} {c : ℝ≥0∞} {ε : ℝ≥0} {d : ℝ}


open EMetric in
lemma coveringNumber_closedBall_le_three_mul {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    [MeasurableSpace E] [BorelSpace E] {ε : ℝ≥0} [Nontrivial E]
    {x : E} {r : ℝ≥0} (hr_zero : r ≠ 0) (hε : ε ≤ r) :
    (coveringNumber ε (Metric.closedEBall x r) : ℝ≥0∞)
      ≤ (3 * r / (ε : ℝ≥0∞)) ^ (Module.finrank ℝ E) := by
  by_cases hε_zero : ε = 0
  · simp only [hε_zero, coveringNumber_zero, Metric.closedEBall_coe, ENNReal.coe_zero]
    rw [ENNReal.div_zero, ENNReal.top_pow]
    · exact le_top
    · exact Module.finrank_ne_zero
    · simp [hr_zero]
  refine (coveringNumber_closedBall_le _ _ _).trans ?_
  let d := Module.finrank ℝ E
  calc (2 * r / (ε : ℝ≥0∞) + 1) ^ d
  _ ≤ (2 * r / (ε : ℝ≥0∞) + r / (ε : ℝ≥0∞)) ^ d := by
    gcongr
    rw [ENNReal.le_div_iff_mul_le (.inl <| mod_cast hε_zero) (.inr (by simp)), one_mul]
    exact mod_cast hε
  _ = (3 * r / (ε : ℝ≥0∞)) ^ d := by
    congr
    rw [← two_add_one_eq_three, add_mul, one_mul, ENNReal.add_div]

set_option backward.isDefEq.respectTransparency false in
open scoped Pointwise in
theorem solution :
    IsCoverWithBoundedCoveringNumber (fun n ↦ Set.Ico (0 : ℝ≥0) (n + 1)) Set.univ
      (fun n ↦ 3 * (n + 1)) (fun _ ↦ 1)  where
  c_ne_top n := by finiteness
  d_pos := by simp
  isOpen n := NNReal.isOpen_Ico_zero
  totallyBounded n := totallyBounded_Ico _ _
  hasBoundedCoveringNumber n := by
    have h_iso : Isometry ((↑) : ℝ≥0 → ℝ) := fun x y ↦ rfl
    have h_image : ((↑) : ℝ≥0 → ℝ) '' (Set.Ico (0 : ℝ≥0) (n + 1)) = Set.Ico (0 : ℝ) (n + 1) := by
      ext x
      simp only [Set.mem_image, Set.mem_Ico, zero_le, true_and]
      refine ⟨fun ⟨y, hy, hy_eq⟩ ↦ ?_, fun h ↦ ?_⟩
      · rw [← hy_eq]
        exact ⟨y.2, hy⟩
      · exact ⟨⟨x, h.1⟩, h.2, rfl⟩
    -- todo : extract that have as a lemma
    have h_diam : Metric.ediam (Set.Ico (0 : ℝ≥0) (n + 1)) = n + 1 := by
      rw [← h_iso.ediam_image, h_image]
      simp only [Real.ediam_Ico, sub_zero]
      norm_cast
    constructor
    · simp [h_diam]
    intro ε hε_le
    simp only [ENNReal.rpow_one]
    rw [← h_iso.coveringNumber_image, h_image]
    rw [h_diam] at hε_le
    have : Set.Ico (0 : ℝ) (n + 1) ⊆ Metric.closedEBall (((n : ℝ) + 1) / 2) ((n + 1) / 2) := by
      intro x hx
      simp only [Set.mem_Ico, Metric.mem_closedEBall, edist_dist, dist] at hx ⊢
      refine ENNReal.ofReal_le_of_le_toReal ?_
      simp only [ENNReal.toReal_div, ENNReal.toReal_ofNat]
      norm_cast
      refine abs_le.mpr ⟨?_, ?_⟩
      · linarith
      · simp [hx.2.le]
    calc (coveringNumber ε (Set.Ico (0 : ℝ) (n + 1)) : ℝ≥0∞)
    _ ≤ coveringNumber (ε / 2) (Metric.closedEBall (((n : ℝ) + 1) / 2) ((n + 1) / 2)) := by
      gcongr
      exact coveringNumber_subset_le this
    _ ≤ 3 * ((n + 1) / 2 : ℝ≥0) / (ε / 2 : ℝ≥0) := by
      have h := coveringNumber_closedBall_le_three_mul (r := (n + 1) / 2) (ε := ε / 2)
        (x := ((n : ℝ) + 1) / 2) ?_ ?_
      · simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, ENNReal.coe_div, ENNReal.coe_add,
          ENNReal.coe_natCast, ENNReal.coe_one, ENNReal.coe_ofNat, Module.finrank_self, pow_one]
          at h
        rwa [ENNReal.coe_div (by simp), ENNReal.coe_div (by simp)]
      · simp
      · gcongr
        exact mod_cast hε_le
    _ = 3 * (n + 1) / ε := by
      conv_lhs => rw [mul_div_assoc]
      conv_rhs => rw [mul_div_assoc]
      congr 1
      simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, ENNReal.coe_div, ENNReal.coe_add,
        ENNReal.coe_natCast, ENNReal.coe_one, ENNReal.coe_ofNat]
      simp_rw [div_eq_mul_inv]
      rw [ENNReal.mul_inv (by simp) (by simp), inv_inv, mul_assoc, mul_comm _ (2 : ℝ≥0∞),
        ← mul_assoc _ (2 : ℝ≥0∞), ENNReal.inv_mul_cancel (by simp) (by simp), one_mul]
    _ ≤ 3 * (n + 1) * (ε : ℝ≥0∞)⁻¹ := by rw [div_eq_mul_inv]
  mono n m hnm x hx := by
    simp only [Set.mem_Ico, zero_le, true_and] at hx ⊢
    exact hx.trans_le (mod_cast (by gcongr))
  subset_iUnion x hx := by
    simp only [Set.mem_iUnion, Set.mem_Ico, zero_le, true_and]
    obtain ⟨i, hi⟩ := exists_nat_gt x
    exact ⟨i, hi.trans (by simp)⟩

