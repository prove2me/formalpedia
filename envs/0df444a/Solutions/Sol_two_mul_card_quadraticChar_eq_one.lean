-- Prove2me | solution 1 for two_mul_card_quadraticChar_eq_one
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T00:56:22.660169+00:00
-- url     : https://prove2.me/submissions/4f9ba5f1-a2e6-47b7-b204-0f5b138e25d5

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
theorem _root_.solution (hF : ringChar F ≠ 2) :
    2 * (univ.filter fun a : F ↦ quadraticChar F a = 1).card + 1 = Fintype.card F := by
  have hval (a : F) : 1 + quadraticChar F a
      = (if a = 0 then 1 else 0) + 2 * if quadraticChar F a = 1 then (1 : ℤ) else 0 := by
    rcases eq_or_ne a 0 with rfl | ha
    · simp
    · rcases quadraticChar_dichotomy ha with h | h <;> simp [h, ha]
  have h : ∑ a : F, (1 + quadraticChar F a) = (Fintype.card F : ℤ) := by
    rw [sum_add_distrib, quadraticChar_sum_zero hF]
    simp
  rw [sum_congr rfl fun a _ ↦ hval a, sum_add_distrib, ← mul_sum, sum_boole, sum_boole] at h
  simp only [filter_eq', mem_univ, ite_true, card_singleton] at h
  omega
