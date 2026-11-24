-- Prove2me | solution 1 for four_mul_card_quadraticChar_sub_eq_one
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T00:57:19.137253+00:00
-- url     : https://prove2.me/submissions/bce573dd-d04c-4ac4-b2bd-f87e5a184a6e

module
public import Definitions.Def_LeanPool_BlockSpectralSensitivity_Defs_Tournament
public import Mathlib.NumberTheory.LegendreSymbol.QuadraticChar.Basic
public import Mathlib.Tactic.NormNum.Prime
public import Definitions.Def_LeanPool_BlockSpectralSensitivity_Paley_Tournament
public import Theorems.Thm_sum_quadraticChar_sub
public import Theorems.Thm_sum_quadraticChar_mul_sub
public import Theorems.Thm_quadraticChar_sub_swap
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


section
@[expose] public section
open Finset
section QuadraticCharSums
variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]
private theorem ne_of_quadraticChar_sub_eq_one {a z : F} (h : quadraticChar F (z - a) = 1) :
    z ≠ a := by
  rintro rfl
  simp at h
private theorem sum_one_add_quadraticChar_sub_mul (hF : ringChar F ≠ 2)
    (hneg : quadraticChar F (-1) = -1) {a b : F} (hab : a ≠ b) :
    ∑ z ∈ (univ.erase a).erase b,
        (1 + quadraticChar F (z - a)) * (1 + quadraticChar F (z - b))
      = (Fintype.card F : ℤ) - 3 := by
  have hpt (z : F) : (1 + quadraticChar F (z - a)) * (1 + quadraticChar F (z - b))
      = 1 + quadraticChar F (z - a) + quadraticChar F (z - b)
        + quadraticChar F ((z - a) * (z - b)) := by
    rw [map_mul]
    ring
  have htot : ∑ z : F, (1 + quadraticChar F (z - a)) * (1 + quadraticChar F (z - b))
      = (Fintype.card F : ℤ) - 1 := by
    rw [sum_congr rfl fun z _ ↦ hpt z, sum_add_distrib, sum_add_distrib, sum_add_distrib,
      sum_quadraticChar_sub hF, sum_quadraticChar_sub hF, sum_quadraticChar_mul_sub hF hab]
    simp [sub_eq_add_neg]
  have hb := sum_erase_add ((univ : Finset F).erase a)
    (fun z ↦ (1 + quadraticChar F (z - a)) * (1 + quadraticChar F (z - b)))
    (mem_erase.mpr ⟨Ne.symm hab, mem_univ b⟩)
  have ha := sum_erase_add (univ : Finset F)
    (fun z ↦ (1 + quadraticChar F (z - a)) * (1 + quadraticChar F (z - b))) (mem_univ a)
  simp only [sub_self, quadraticChar_zero, add_zero, mul_one, one_mul] at hb ha
  rw [htot, quadraticChar_sub_swap hneg a b] at ha
  omega
private theorem one_add_quadraticChar_sub_mul_eq_ite {a b z : F} (hz : z ≠ a) (hz' : z ≠ b) :
    (1 + quadraticChar F (z - a)) * (1 + quadraticChar F (z - b))
      = if quadraticChar F (z - a) = 1 ∧ quadraticChar F (z - b) = 1 then 4 else 0 := by
  by_cases hc : quadraticChar F (z - a) = 1 ∧ quadraticChar F (z - b) = 1
  · rw [if_pos hc, hc.1, hc.2]
    norm_num only
  · rw [if_neg hc]
    rcases not_and_or.mp hc with h' | h'
    · rw [(quadraticChar_eq_neg_one_iff_not_one (sub_ne_zero.mpr hz)).mpr h']
      ring
    · rw [(quadraticChar_eq_neg_one_iff_not_one (sub_ne_zero.mpr hz')).mpr h']
      ring
end QuadraticCharSums
namespace BSLambda
section Paley
end Paley
end BSLambda
end
end

set_option autoImplicit true
@[expose] public section
public section
open Finset
variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]
theorem _root_.solution (hF : ringChar F ≠ 2)
    (hneg : quadraticChar F (-1) = -1) {a b : F} (hab : a ≠ b) :
    4 * (univ.filter fun z : F ↦
        quadraticChar F (z - a) = 1 ∧ quadraticChar F (z - b) = 1).card + 3
      = Fintype.card F := by
  have hset : ((univ.erase a).erase b).filter
      (fun z : F ↦ quadraticChar F (z - a) = 1 ∧ quadraticChar F (z - b) = 1)
      = univ.filter fun z : F ↦ quadraticChar F (z - a) = 1 ∧ quadraticChar F (z - b) = 1 := by
    ext z
    simp only [mem_filter, mem_erase, mem_univ, true_and, and_true, and_iff_right_iff_imp]
    exact fun hz ↦ ⟨ne_of_quadraticChar_sub_eq_one hz.2, ne_of_quadraticChar_sub_eq_one hz.1⟩
  have h := sum_one_add_quadraticChar_sub_mul hF hneg hab
  rw [sum_congr rfl fun z hz ↦ one_add_quadraticChar_sub_mul_eq_ite
      (ne_of_mem_erase (mem_erase.mp hz).2) (ne_of_mem_erase hz), ← sum_filter, hset, sum_const,
    nsmul_eq_mul] at h
  omega
