-- Prove2me | solution 1 for sum_quadraticChar_mul_sub
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T00:56:20.918031+00:00
-- url     : https://prove2.me/submissions/2d0f915b-f272-47ff-ba1d-9944ed62d99e

module
public import Definitions.Def_LeanPool_BlockSpectralSensitivity_Defs_Tournament
public import Mathlib.NumberTheory.LegendreSymbol.QuadraticChar.Basic
public import Mathlib.Tactic.NormNum.Prime
public import Definitions.Def_LeanPool_BlockSpectralSensitivity_Paley_Tournament
public import Theorems.Thm_BSLambda_mem_commonIn
public import Theorems.Thm_BSLambda_mem_commonOut
public import Theorems.Thm_BSLambda_mem_inNbrs
public import Theorems.Thm_BSLambda_mem_middles
public import Theorems.Thm_BSLambda_mem_outNbrs
attribute [local simp] BSLambda.mem_commonIn
attribute [local simp] BSLambda.mem_commonOut
attribute [local simp] BSLambda.mem_inNbrs
attribute [local simp] BSLambda.mem_middles
attribute [local simp] BSLambda.mem_outNbrs



set_option autoImplicit true
@[expose] public section
public section
open Finset
variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]
theorem _root_.solution (hF : ringChar F ≠ 2) {a b : F} (hab : a ≠ b) :
    ∑ z : F, quadraticChar F ((z - a) * (z - b)) = -1 := by
  have hba : b - a ≠ 0 := sub_ne_zero.mpr (Ne.symm hab)
  have hza {z : F} (hz : z ∈ univ.erase a) : z - a ≠ 0 := sub_ne_zero.mpr (mem_erase.mp hz).1
  have hw1 {w : F} (hw : w ∈ univ.erase (1 : F)) : (1 : F) - w ≠ 0 :=
    sub_ne_zero.mpr (Ne.symm (mem_erase.mp hw).1)
  have hone {z : F} (h : z - a ≠ 0) : (1 : F) - (z - b) / (z - a) = (b - a) / (z - a) := by
    field_simp [h]
    ring
  have hsq {z : F} (h : z - a ≠ 0) : (z - a) * (z - b) = (z - a) ^ 2 * ((z - b) / (z - a)) := by
    field_simp [h]
  have hinva {w : F} (h : (1 : F) - w ≠ 0) : (b - w * a) / (1 - w) - a = (b - a) / (1 - w) := by
    field_simp [h]
    ring
  have hinvb {w : F} (h : (1 : F) - w ≠ 0) :
      (b - w * a) / (1 - w) - b = w * (b - a) / (1 - w) := by
    field_simp [h]
    ring
  have key : ∑ z ∈ univ.erase a, quadraticChar F ((z - a) * (z - b))
      = ∑ w ∈ univ.erase 1, quadraticChar F w := by
    refine sum_nbij' (fun z ↦ (z - b) / (z - a)) (fun w ↦ (b - w * a) / (1 - w))
      ?_ ?_ ?_ ?_ ?_
    · intro z hz
      simp only [mem_erase, mem_univ, and_true]
      rw [Ne, div_eq_one_iff_eq (hza hz)]
      intro h
      apply hab
      linear_combination h
    · intro w hw
      simp only [mem_erase, mem_univ, and_true]
      refine sub_ne_zero.mp ?_
      rw [hinva (hw1 hw)]
      exact div_ne_zero hba (hw1 hw)
    · intro z hz
      rw [hone (hza hz), div_eq_iff (div_ne_zero hba (hza hz))]
      field_simp [hza hz]
      ring
    · intro w hw
      rw [hinva (hw1 hw), hinvb (hw1 hw), div_div_div_cancel_right₀ (hw1 hw), mul_div_assoc,
        div_self hba, mul_one]
    · intro z hz
      rw [hsq (hza hz), map_mul, quadraticChar_sq_one' (hza hz), one_mul]
  have hleft : ∑ z ∈ univ.erase a, quadraticChar F ((z - a) * (z - b))
      = ∑ z : F, quadraticChar F ((z - a) * (z - b)) :=
    sum_erase _ (by simp)
  have hright : ∑ w ∈ univ.erase 1, quadraticChar F w = -1 := by
    have h := sum_erase_add (univ : Finset F) (fun w ↦ quadraticChar F w) (mem_univ (1 : F))
    rw [quadraticChar_sum_zero hF] at h
    simp only [MulChar.map_one] at h
    omega
  rw [← hleft, key, hright]
