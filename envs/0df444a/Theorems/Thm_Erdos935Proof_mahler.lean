-- Prove2me | Theorems.Thm_Erdos935Proof_mahler
-- name    : Erdos935Proof.mahler
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T12:39:04.14725+00:00
-- url     : https://prove2.me/theorems/52abf35f-8b19-4e49-8838-f072512f2c4e
-- title:
--   Erdos935 Proof: mahler
-- statement:
--   The bound implied by a result of Mahler: for $\ell \geq 1$,
--   $\limsup Q_2(n(n+1)\cdots(n+\ell))/n^2 \geq 1$.
--
--   Source: https://github.com/veljjanoski/erdos935-palomar/blob/80decbdd1cca367db2185caf5e62acefc28a71d6/Solution.lean#L164-L200
-- source:
--   https://github.com/veljjanoski/erdos935-palomar/blob/80decbdd1cca367db2185caf5e62acefc28a71d6/Solution.lean#L164-L200

module
public import Mathlib
public import Definitions.Def_Erdos935Palomar_Solution
set_option autoImplicit true
@[expose] public section
public section
open Filter
open Erdos935Proof

theorem Erdos935Proof.mahler : ∀ ℓ : ℕ, 1 ≤ ℓ → ∀ ε : ℝ, 0 < ε → ∃ᶠ n : ℕ in atTop,
    (1 - ε) * (n : ℝ) ^ 2 <
      ((Erdos367.B 2 (∏ m ∈ Finset.Icc n (n + ℓ), m) : ℕ) : ℝ) := by sorry
