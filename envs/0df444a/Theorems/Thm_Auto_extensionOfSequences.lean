-- Prove2me | Theorems.Thm_Auto_extensionOfSequences
-- name    : Auto.extensionOfSequences
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T14:59:24.607985+00:00
-- url     : https://prove2.me/theorems/f7ceeebf-54fb-4f76-aa1b-8631e08d7cdd
-- title:
--   Auto: extension Of Sequences
-- statement:
--   **Proposition (Extension of sequences).**
--
--   Let $J\in\mathbb{N}$ with $J\ge1$ and let $a:[J)\to\mathbb{R}$ satisfy $a(j)>0$ for every $j\in[J)$
--   and, for all $j\in[J-1)$, we have $a(j+1)\ge 2a(j)$.
--   Then there is a unique $b\in A$ such that for all $j\in [J)$ we have $a(j)=b(j)$ and for $j\ge J$ we
--   have $b(j)=2^{j-J+1} a(J-1)$ and for $j<0$ we have $b(j)=2^j a(0)$\, .
--
--   Source: https://github.com/roos-j/lean-nct/blob/3e09aa52c478ec69abb02eb250c5e5ed06653c3a/LeanNct/Auto/Preliminaries/MultiplicativelySpacedMonotoneSequences.lean#L107-L204
-- source:
--   https://github.com/roos-j/lean-nct/blob/3e09aa52c478ec69abb02eb250c5e5ed06653c3a/LeanNct/Auto/Preliminaries/MultiplicativelySpacedMonotoneSequences.lean#L107-L204

module
public import Mathlib
public import Definitions.Def_LeanNct_Auto_Preliminaries_MultiplicativelySpacedMonotoneSequences
set_option autoImplicit true
@[expose] public section
public section
open Auto
open Set

theorem Auto.extensionOfSequences (J : ℕ) (hJ : 0 < J) (a : ℤ → ℝ)
    (ha_pos : ∀ j : ℤ, 0 ≤ j → j < (J : ℤ) → 0 < a j)
    (ha_space : ∀ j : ℤ, 0 ≤ j → j + 1 < (J : ℤ) → 2 * a j ≤ a (j + 1)) :
    ∃! b : ℤ → ℝ, SpacedSequence b ∧
      (∀ j : ℤ, 0 ≤ j → j < (J : ℤ) → b j = a j) ∧
      (∀ j : ℤ, (J : ℤ) ≤ j → b j = (2 : ℝ) ^ (j - J + 1) * a (J - 1)) ∧
      (∀ j : ℤ, j < 0 → b j = (2 : ℝ) ^ j * a 0) := by sorry
