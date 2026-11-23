-- Prove2me | solution 1 for sum_pos_iff_exists_pos
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T06:39:40.091416+00:00
-- url     : https://prove2.me/submissions/630dd176-da8b-4a68-acd8-4cd16d54f12d

module
public import Mathlib.Algebra.Order.BigOperators.Group.List
public import Mathlib.Data.Nat.Basic
public import Mathlib.Tactic
public import Definitions.Def_Apportionmentlib_Utils

set_option autoImplicit false
@[expose] public section
public section
theorem _root_.solution {n : ℕ} {v : Vector ℕ n} : 0 < v.sum ↔ ∃ i : Fin n, 0 < v[i] := by
  rw [← Vector.sum_toList]
  constructor
  · contrapose!
    intro h_nonpos
    rw [nonpos_iff_eq_zero, List.sum_eq_zero_iff]
    intro x hx
    obtain ⟨i, h, rfl⟩ := Vector.mem_iff_getElem.mp (Vector.mem_toList_iff.mp hx)
    exact Nat.le_zero.mp (h_nonpos ⟨i, h⟩)
  · intro ⟨i, hi⟩
    have : v[i] ≤ v.toList.sum := List.le_sum_of_mem (by simp)
    omega
