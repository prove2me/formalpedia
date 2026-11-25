-- Prove2me | Theorems.Thm_Erdos393Proof_abc_dichotomy
-- name    : Erdos393Proof.abc_dichotomy
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T15:31:56.383003+00:00
-- url     : https://prove2.me/theorems/83ce461d-03d7-52b6-8b00-e2d9dfa460fd
-- title:
--   Erdos393 Proof: abc dichotomy
-- statement:
--   The abc conjecture in the form used below: a coprime sum `u + v = w` has `w` bounded or
--   `w ≤ rad(uvw)^(1+ε)`.
--
--   Source: https://github.com/veljjanoski/erdos393-palomar/blob/ec05768609980a27995453bc1701e6fa3004d675/Solution.lean#L150-L168
-- source:
--   https://github.com/veljjanoski/erdos393-palomar/blob/ec05768609980a27995453bc1701e6fa3004d675/Solution.lean#L150-L168

module
public import Mathlib
public import Definitions.Def_Erdos393Palomar_Solution
set_option autoImplicit true
@[expose] public section
public section
open Filter Asymptotics
open scoped Nat
open Erdos393Proof
open ABC Polynomial

theorem Erdos393Proof.abc_dichotomy (habc : AbcHyp) (ε : ℝ) (hε : 0 < ε) :
    ∃ cmax : ℕ, ∀ u v w : ℕ, 0 < u → 0 < v → Nat.Coprime u v → u + v = w →
      w ≤ cmax ∨ (w : ℝ) ≤ (radical (u * v * w) : ℝ) ^ (1 + ε) := by sorry
