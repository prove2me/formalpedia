-- Prove2me | solution 1 for ramanujanNagellExact
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-20T22:45:23.072172+00:00
-- url     : https://prove2.me/submissions/b392daaf-cef4-417a-b801-c51a5bd0009b

module
public import Definitions.Def_LeanPool_RamanujanNagell_Helpers
public import Mathlib.Data.Nat.Totient
public import Mathlib.Data.Sym.Sym2.Init
public import Mathlib.NumberTheory.Multiplicity
public import Mathlib.RingTheory.Int.Basic
public import Mathlib.Tactic.LinearCombination
public import Mathlib.Tactic.NormNum.GCD
public import Definitions.Def_LeanPool_RamanujanNagell_Basic

set_option autoImplicit true
@[expose] public section
public section
open RamanujanNagell
theorem _root_.solution :
  ∀ x : ℤ, ∀ n : ℕ, x ^ 2 + 7 = 2 ^ n ↔
    (x, n) = (1, 3) ∨ (x, n) = (-1, 3)
  ∨ (x, n) = (3, 4) ∨ (x, n) = (-3, 4)
  ∨ (x, n) = (5, 5) ∨ (x, n) = (-5, 5)
  ∨ (x, n) = (11, 7) ∨ (x, n) = (-11, 7)
  ∨ (x, n) = (181, 15) ∨ (x, n) = (-181, 15) := by
  intro x n
  constructor
  · exact RamanujanNagell x n
  · intro h
    rcases h with h | h | h | h | h | h | h | h | h | h <;>
      (rw [Prod.mk.injEq] at h; obtain ⟨hx, hn⟩ := h; subst hx; subst hn; norm_num)
