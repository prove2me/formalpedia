-- Prove2me | Theorems.Thm_Erdos935Proof_parts_ii
-- name    : Erdos935Proof.parts_ii
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T12:38:54.151928+00:00
-- url     : https://prove2.me/theorems/2be3c56c-13d5-48b9-84f4-6a5fd5ead964
-- title:
--   Erdos935 Proof: parts ii
-- statement:
--   The second part of Erdős Problem 935: for $\ell \geq 2$,
--   $\limsup Q_2(n(n+1)\cdots(n+\ell))/n^2 = \infty$.
--
--   Source: https://github.com/veljjanoski/erdos935-palomar/blob/80decbdd1cca367db2185caf5e62acefc28a71d6/Solution.lean#L112-L155
-- source:
--   https://github.com/veljjanoski/erdos935-palomar/blob/80decbdd1cca367db2185caf5e62acefc28a71d6/Solution.lean#L112-L155

module
public import Mathlib
public import Definitions.Def_Erdos935Palomar_Solution
set_option autoImplicit true
@[expose] public section
public section
open Filter
open Erdos935Proof

theorem Erdos935Proof.parts_ii : ∀ ℓ : ℕ, 2 ≤ ℓ → ∀ C : ℝ, ∃ᶠ n : ℕ in atTop,
    C * (n : ℝ) ^ 2 < ((Erdos367.B 2 (∏ m ∈ Finset.Icc n (n + ℓ), m) : ℕ) : ℝ) := by sorry
