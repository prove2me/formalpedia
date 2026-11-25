-- Prove2me | Theorems.Thm_Erdos393Proof_natAbs_eval_le
-- name    : Erdos393Proof.natAbs_eval_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T15:22:52.258802+00:00
-- url     : https://prove2.me/theorems/52119a46-3ac0-4411-a057-23c5e7b17d3f
-- title:
--   Erdos393 Proof: nat Abs eval le
-- statement:
--   A polynomial value is at most the sum of the absolute coefficients times `y ^ deg`.
--
--   Source: https://github.com/veljjanoski/erdos393-palomar/blob/ec05768609980a27995453bc1701e6fa3004d675/Solution.lean#L112-L124
-- source:
--   https://github.com/veljjanoski/erdos393-palomar/blob/ec05768609980a27995453bc1701e6fa3004d675/Solution.lean#L112-L124

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

theorem Erdos393Proof.natAbs_eval_le (R : ℤ[X]) {y : ℕ} (hy : 1 ≤ y) :
    (R.eval (y : ℤ)).natAbs ≤
      (∑ i ∈ Finset.range (R.natDegree + 1), (R.coeff i).natAbs) * y ^ R.natDegree := by sorry
