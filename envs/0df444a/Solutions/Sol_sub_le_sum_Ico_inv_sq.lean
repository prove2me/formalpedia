-- Prove2me | solution 1 for sub_le_sum_Ico_inv_sq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T19:27:54.615161+00:00
-- url     : https://prove2.me/submissions/8e60f8e1-6746-4795-8422-129522d31806

module
public import Definitions.Def_Fekete_Window
public import Mathlib.Analysis.PSeries
public import Definitions.Def_Fekete_DeBruijnErdos

set_option autoImplicit true
@[expose] public section
public section
noncomputable section
open Filter Finset
open scoped Topology
variable {α : Type*} [Field α] [LinearOrder α] [IsStrictOrderedRing α]
theorem _root_.solution {k n : ℕ} (hk : k ≠ 0) (h : k ≤ n) :
    (k : α)⁻¹ - (n : α)⁻¹ ≤ ∑ i ∈ Ico k n, ((i : α) ^ 2)⁻¹ := by
  refine Nat.le_induction ?_ ?_ n h
  · simp
  intro n hn IH
  rw [sum_Ico_succ_top hn]
  suffices (n : α)⁻¹ - ((n + 1 : ℕ) : α)⁻¹ ≤ ((n : α) ^ 2)⁻¹ by linarith
  have A : 0 < (n : α) := by simpa using (Nat.pos_of_ne_zero hk).trans_le hn
  push_cast
  field_simp
  linarith
