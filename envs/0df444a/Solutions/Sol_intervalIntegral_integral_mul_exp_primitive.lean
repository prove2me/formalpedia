-- Prove2me | solution 1 for intervalIntegral.integral_mul_exp_primitive
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-30T12:32:24.888296+00:00
-- url     : https://prove2.me/submissions/90d51d25-1f97-4a49-ac56-47a4bca2ab2f

import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.MeasureTheory.Group.Prod
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Integral.Prod

/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

/-!
# Exponential of an integral primitive

This file proves the integral identity for the exponential of the primitive of a bounded
nonnegative integrable real function.  The proof compares the integral with left and right sums
on uniform partitions; in particular, it does not require pointwise differentiability of the
primitive.

Main results: `intervalIntegral.integral_mul_exp_primitive`,
`intervalIntegral.lintegral_timeTriangle_sub`, and `intervalIntegral.integral_timeTriangle_sub`.

No probabilistic structure is used or asserted.
-/

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
open scoped ENNReal

namespace intervalIntegral

noncomputable section

-- The namespace placement is upstream-facing: this is a pure companion to interval integrals.




private theorem exp_mul_sub_le_sub_exp {x y : ℝ} :
    Real.exp x * (y - x) ≤ Real.exp y - Real.exp x := by
  rw [le_sub_iff_add_le]
  calc
    Real.exp x * (y - x) + Real.exp x = Real.exp x * ((y - x) + 1) := by ring
    _ ≤ Real.exp x * Real.exp (y - x) :=
      mul_le_mul_of_nonneg_left (Real.add_one_le_exp (y - x)) (Real.exp_pos x).le
    _ = Real.exp y := by
      rw [← Real.exp_add]
      congr 1
      ring

private theorem sub_exp_le_exp_mul_sub {x y : ℝ} :
    Real.exp y - Real.exp x ≤ Real.exp y * (y - x) := by
  have h := mul_le_mul_of_nonneg_left (Real.add_one_le_exp (x - y)) (Real.exp_pos y).le
  have h' : Real.exp y * ((x - y) + 1) ≤ Real.exp x := by
    calc
      Real.exp y * ((x - y) + 1) ≤ Real.exp y * Real.exp (x - y) := h
      _ = Real.exp x := by
        rw [← Real.exp_add]
        congr 1
        ring
  rw [sub_le_iff_le_add]
  calc
    Real.exp y = Real.exp y * ((x - y) + 1) + Real.exp y * (y - x) := by ring
    _ ≤ Real.exp x + Real.exp y * (y - x) := by
      simpa only [add_comm] using add_le_add_right h' (Real.exp y * (y - x))
    _ = Real.exp y * (y - x) + Real.exp x := add_comm _ _



end

end intervalIntegral


open intervalIntegral
/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

/-!
# Exponential of an integral primitive

This file proves the integral identity for the exponential of the primitive of a bounded
nonnegative integrable real function.  The proof compares the integral with left and right sums
on uniform partitions; in particular, it does not require pointwise differentiability of the
primitive.

Main results: `intervalIntegral.integral_mul_exp_primitive`,
`intervalIntegral.lintegral_timeTriangle_sub`, and `intervalIntegral.integral_timeTriangle_sub`.

No probabilistic structure is used or asserted.
-/

open MeasureTheory Set
open scoped ENNReal



-- The namespace placement is upstream-facing: this is a pure companion to interval integrals.








namespace intervalIntegral

end intervalIntegral
open intervalIntegral
theorem solution {a : ℝ → ℝ} {C T t : ℝ}
    (ht : t ∈ Icc (0 : ℝ) T)
    (ha : IntegrableOn a (Icc (0 : ℝ) T))
    (ha_nonneg : ∀ s ∈ Icc (0 : ℝ) T, 0 ≤ a s)
    (ha_le : ∀ s ∈ Icc (0 : ℝ) T, a s ≤ C) :
    (∫ s in (0 : ℝ)..t, a s * Real.exp (∫ r in (0 : ℝ)..s, a r)) =
      Real.exp (∫ r in (0 : ℝ)..t, a r) - 1 := by
  have hT : 0 ≤ T := ht.1.trans ht.2
  have hC : 0 ≤ C := (ha_nonneg 0 ⟨le_rfl, hT⟩).trans (ha_le 0 ⟨le_rfl, hT⟩)
  let A : ℝ → ℝ := fun s ↦ ∫ r in (0 : ℝ)..s, a r
  have hInt0T : IntervalIntegrable a volume (0 : ℝ) T := by
    rw [intervalIntegrable_iff, uIoc_of_le hT]
    exact ha.mono_set Ioc_subset_Icc_self
  have hInt (u v : ℝ) (hu : u ∈ Icc (0 : ℝ) T) (hv : v ∈ Icc (0 : ℝ) T) :
      IntervalIntegrable a volume u v := by
    apply hInt0T.mono_set
    rw [uIcc_of_le hT]
    intro z hz
    rw [mem_uIcc] at hz
    rcases hz with hz | hz
    · exact ⟨hu.1.trans hz.1, hz.2.trans hv.2⟩
    · exact ⟨hv.1.trans hz.1, hz.2.trans hu.2⟩
  have hA_sub (u v : ℝ) (hu : u ∈ Icc (0 : ℝ) T) (hv : v ∈ Icc (0 : ℝ) T) :
      A v - A u = ∫ r in u..v, a r := by
    exact integral_interval_sub_left (hInt 0 v ⟨le_rfl, hT⟩ hv)
      (hInt 0 u ⟨le_rfl, hT⟩ hu)
  have hA_mono (u v : ℝ) (hu : u ∈ Icc (0 : ℝ) T) (hv : v ∈ Icc (0 : ℝ) T)
      (huv : u ≤ v) : A u ≤ A v := by
    rw [← sub_nonneg, hA_sub u v hu hv]
    exact integral_nonneg huv fun s hs ↦ ha_nonneg s ⟨hu.1.trans hs.1, hs.2.trans hv.2⟩
  have hA_inc_le (u v : ℝ) (hu : u ∈ Icc (0 : ℝ) T) (hv : v ∈ Icc (0 : ℝ) T)
      (huv : u ≤ v) : A v - A u ≤ C * (v - u) := by
    rw [hA_sub u v hu hv]
    calc
      (∫ r in u..v, a r) ≤ ∫ _r in u..v, C := by
        apply integral_mono_on huv (hInt u v hu hv)
          (continuousOn_const.intervalIntegrable)
        intro s hs
        exact ha_le s ⟨hu.1.trans hs.1, hs.2.trans hv.2⟩
      _ = C * (v - u) := by
        rw [intervalIntegral.integral_const, smul_eq_mul]
        ring
  have hAcont : ContinuousOn A (Icc (0 : ℝ) T) := by
    rw [← uIcc_of_le hT]
    exact continuousOn_primitive_interval' hInt0T left_mem_uIcc
  have hExpAcont : ContinuousOn (fun s ↦ Real.exp (A s)) (Icc (0 : ℝ) T) :=
    Real.continuous_exp.comp_continuousOn hAcont
  have hTargetInt : IntervalIntegrable (fun s ↦ a s * Real.exp (A s)) volume 0 t := by
    exact (hInt 0 t ⟨le_rfl, hT⟩ ht).mul_continuousOn
      (hExpAcont.mono (by
        rw [uIcc_of_le ht.1]
        exact Icc_subset_Icc le_rfl ht.2))
  have hA0 : A 0 = 0 := integral_same
  have hExpIncNonneg : 0 ≤ Real.exp (A t) - 1 := by
    rw [← Real.exp_zero, sub_nonneg, Real.exp_le_exp]
    rw [← hA0]
    exact hA_mono 0 t ⟨le_rfl, hT⟩ ht ht.1
  let B : ℝ := C * t * (Real.exp (A t) - 1)
  have hB : 0 ≤ B := mul_nonneg (mul_nonneg hC ht.1) hExpIncNonneg
  have hApprox (N : ℕ) (hN : 0 < N) :
      (∫ s in (0 : ℝ)..t, a s * Real.exp (A s)) ≤
          Real.exp (A t) - 1 + B / N ∧
        Real.exp (A t) - 1 ≤
          (∫ s in (0 : ℝ)..t, a s * Real.exp (A s)) + B / N := by
    let p : ℕ → ℝ := fun j ↦ (j : ℝ) * t / N
    have hNreal : (0 : ℝ) < N := by exact_mod_cast hN
    have hp0 : p 0 = 0 := by simp only [CharP.cast_eq_zero, zero_mul, zero_div, p]
    have hpN : p N = t := by
      simp only [ne_eq, Nat.cast_eq_zero, hN.ne', not_false_eq_true,
        mul_div_cancel_left₀, p]
    have hp_le_t (j : ℕ) (hj : j ≤ N) : p j ≤ t := by
      rw [div_le_iff₀ hNreal]
      calc
        (j : ℝ) * t ≤ (N : ℝ) * t :=
          mul_le_mul_of_nonneg_right (by exact_mod_cast hj) ht.1
        _ = t * N := mul_comm _ _
    have hp_mem (j : ℕ) (hj : j ≤ N) : p j ∈ Icc (0 : ℝ) T := by
      constructor
      · exact div_nonneg (mul_nonneg (Nat.cast_nonneg j) ht.1) hNreal.le
      · exact (hp_le_t j hj).trans ht.2
    have hp_mono (j : ℕ) (hj : j < N) : p j ≤ p (j + 1) := by
      rw [div_le_div_iff_of_pos_right hNreal]
      exact mul_le_mul_of_nonneg_right (by exact_mod_cast Nat.le_succ j) ht.1
    have hp_succ_mem (j : ℕ) (hj : j < N) : p (j + 1) ∈ Icc (0 : ℝ) T :=
      hp_mem (j + 1) hj
    let I : ℕ → ℝ := fun j ↦ ∫ s in p j..p (j + 1), a s
    let L : ℝ := ∑ j ∈ Finset.range N, Real.exp (A (p j)) * I j
    let R : ℝ := ∑ j ∈ Finset.range N, Real.exp (A (p (j + 1))) * I j
    have hI_eq (j : ℕ) (hj : j < N) : I j = A (p (j + 1)) - A (p j) := by
      simp only [I]
      exact (hA_sub (p j) (p (j + 1)) (hp_mem j hj.le) (hp_succ_mem j hj)).symm
    have hI_nonneg (j : ℕ) (hj : j < N) : 0 ≤ I j := by
      rw [hI_eq j hj, sub_nonneg]
      exact hA_mono (p j) (p (j + 1)) (hp_mem j hj.le) (hp_succ_mem j hj)
        (hp_mono j hj)
    have hI_le (j : ℕ) (hj : j < N) : I j ≤ C * (t / N) := by
      rw [hI_eq j hj]
      calc
        A (p (j + 1)) - A (p j) ≤ C * (p (j + 1) - p j) :=
          hA_inc_le (p j) (p (j + 1)) (hp_mem j hj.le) (hp_succ_mem j hj)
            (hp_mono j hj)
        _ = C * (t / N) := by
          dsimp only [p]
          rw [Nat.cast_add, Nat.cast_one]
          ring
    have hTel : (∑ j ∈ Finset.range N,
        (Real.exp (A (p (j + 1))) - Real.exp (A (p j)))) = Real.exp (A t) - 1 := by
      calc
        (∑ j ∈ Finset.range N,
            (Real.exp (A (p (j + 1))) - Real.exp (A (p j)))) =
            Real.exp (A (p N)) - Real.exp (A (p 0)) :=
              Finset.sum_range_sub (fun j ↦ Real.exp (A (p j))) N
        _ = Real.exp (A t) - 1 := by rw [hpN, hp0, hA0, Real.exp_zero]
    have hL_center : L ≤ Real.exp (A t) - 1 := by
      simp only [L]
      rw [← hTel]
      apply Finset.sum_le_sum
      intro j hj
      rw [Finset.mem_range] at hj
      rw [hI_eq j hj]
      exact exp_mul_sub_le_sub_exp
    have hCenter_R : Real.exp (A t) - 1 ≤ R := by
      simp only [R]
      rw [← hTel]
      apply Finset.sum_le_sum
      intro j hj
      rw [Finset.mem_range] at hj
      rw [hI_eq j hj]
      exact sub_exp_le_exp_mul_sub
    have hCellInt (j : ℕ) (hj : j < N) :
        IntervalIntegrable (fun s ↦ a s * Real.exp (A s)) volume (p j) (p (j + 1)) :=
      hTargetInt.mono_set (by
        rw [uIcc_of_le (hp_mono j hj), uIcc_of_le ht.1]
        exact Icc_subset_Icc (hp_mem j hj.le).1 (hp_le_t (j + 1) hj))
    have hL_target : L ≤ ∫ s in (0 : ℝ)..t, a s * Real.exp (A s) := by
      simp only [L]
      rw [← hp0, ← hpN]
      rw [← sum_integral_adjacent_intervals (fun j hj ↦ hCellInt j hj)]
      apply Finset.sum_le_sum
      intro j hj
      rw [Finset.mem_range] at hj
      rw [← intervalIntegral.integral_const_mul]
      apply integral_mono_on (hp_mono j hj)
      · exact (hInt (p j) (p (j + 1)) (hp_mem j hj.le) (hp_succ_mem j hj)).const_mul _
      · exact hCellInt j hj
      intro s hs
      simpa only [mul_comm] using mul_le_mul_of_nonneg_left
        (Real.exp_le_exp.mpr (hA_mono (p j) s (hp_mem j hj.le)
          ⟨(hp_mem j hj.le).1.trans hs.1, hs.2.trans (hp_succ_mem j hj).2⟩ hs.1))
        (ha_nonneg s ⟨(hp_mem j hj.le).1.trans hs.1,
          hs.2.trans (hp_succ_mem j hj).2⟩)
    have hTarget_R : (∫ s in (0 : ℝ)..t, a s * Real.exp (A s)) ≤ R := by
      simp only [R]
      rw [← hp0, ← hpN]
      rw [← sum_integral_adjacent_intervals (fun j hj ↦ hCellInt j hj)]
      apply Finset.sum_le_sum
      intro j hj
      rw [Finset.mem_range] at hj
      rw [← intervalIntegral.integral_const_mul]
      apply integral_mono_on (hp_mono j hj)
      · exact hCellInt j hj
      · exact (hInt (p j) (p (j + 1)) (hp_mem j hj.le) (hp_succ_mem j hj)).const_mul _
      intro s hs
      simpa only [mul_comm] using mul_le_mul_of_nonneg_left
        (Real.exp_le_exp.mpr (hA_mono s (p (j + 1))
          ⟨(hp_mem j hj.le).1.trans hs.1, hs.2.trans (hp_succ_mem j hj).2⟩
          (hp_succ_mem j hj) hs.2))
        (ha_nonneg s ⟨(hp_mem j hj.le).1.trans hs.1,
          hs.2.trans (hp_succ_mem j hj).2⟩)
    have hGap : R - L ≤ B / N := by
      simp only [R, L]
      rw [← Finset.sum_sub_distrib]
      calc
        (∑ j ∈ Finset.range N,
            (Real.exp (A (p (j + 1))) * I j - Real.exp (A (p j)) * I j)) =
            ∑ j ∈ Finset.range N,
              (Real.exp (A (p (j + 1))) - Real.exp (A (p j))) * I j := by
                apply Finset.sum_congr rfl
                intro j _
                ring
        _ ≤ ∑ j ∈ Finset.range N,
              (Real.exp (A (p (j + 1))) - Real.exp (A (p j))) * (C * (t / N)) := by
                apply Finset.sum_le_sum
                intro j hj
                rw [Finset.mem_range] at hj
                exact mul_le_mul_of_nonneg_left (hI_le j hj)
                  (sub_nonneg.mpr (Real.exp_le_exp.mpr
                    (hA_mono (p j) (p (j + 1)) (hp_mem j hj.le)
                      (hp_succ_mem j hj) (hp_mono j hj))))
        _ = B / N := by
              rw [← Finset.sum_mul, hTel]
              dsimp only [B]
              ring
    have hR_le : R ≤ L + B / N := by linarith only [hGap]
    constructor
    · calc
        (∫ s in (0 : ℝ)..t, a s * Real.exp (A s)) ≤ R := hTarget_R
        _ ≤ L + B / N := hR_le
        _ ≤ Real.exp (A t) - 1 + B / N := by
          simpa only [add_comm] using add_le_add_right hL_center (B / N)
    · calc
        Real.exp (A t) - 1 ≤ R := hCenter_R
        _ ≤ L + B / N := hR_le
        _ ≤ (∫ s in (0 : ℝ)..t, a s * Real.exp (A s)) + B / N := by
          simpa only [add_comm] using add_le_add_right hL_target (B / N)
  change (∫ s in (0 : ℝ)..t, a s * Real.exp (A s)) = Real.exp (A t) - 1
  apply le_antisymm
  · refine le_of_forall_pos_le_add fun epsilon hepsilon ↦ ?_
    obtain ⟨N, hN⟩ := exists_nat_gt (B / epsilon)
    have hNposReal : (0 : ℝ) < N := (div_nonneg hB hepsilon.le).trans_lt hN
    have hNpos : 0 < N := by exact_mod_cast hNposReal
    have hBN : B / N < epsilon := by
      rw [div_lt_iff₀ hNposReal]
      have := (div_lt_iff₀ hepsilon).mp hN
      nlinarith only [this]
    exact (hApprox N hNpos).1.trans (add_le_add_right hBN.le _)
  · refine le_of_forall_pos_le_add fun epsilon hepsilon ↦ ?_
    obtain ⟨N, hN⟩ := exists_nat_gt (B / epsilon)
    have hNposReal : (0 : ℝ) < N := (div_nonneg hB hepsilon.le).trans_lt hN
    have hNpos : 0 < N := by exact_mod_cast hNposReal
    have hBN : B / N < epsilon := by
      rw [div_lt_iff₀ hNposReal]
      have := (div_lt_iff₀ hepsilon).mp hN
      nlinarith only [this]
    exact (hApprox N hNpos).2.trans (add_le_add_right hBN.le _)
