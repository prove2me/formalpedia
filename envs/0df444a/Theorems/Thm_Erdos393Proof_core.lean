-- Prove2me | Theorems.Thm_Erdos393Proof_core
-- name    : Erdos393Proof.core
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T15:32:18.638798+00:00
-- url     : https://prove2.me/theorems/c083b51e-9100-468a-b569-80f622091a25
-- title:
--   Erdos393 Proof: core
-- statement:
--   The core of Luca's argument. If `y^d + y^k R(y) = d^d n!` with `R(0) ≠ 0` and
--   `k + deg R ≤ d − 2`, and `y^d ≥ n!`, then `n!` is at most an exponential in `n`.
--
--   Source: https://github.com/veljjanoski/erdos393-palomar/blob/ec05768609980a27995453bc1701e6fa3004d675/Solution.lean#L174-L360
-- source:
--   https://github.com/veljjanoski/erdos393-palomar/blob/ec05768609980a27995453bc1701e6fa3004d675/Solution.lean#L174-L360

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

theorem Erdos393Proof.core (habc : AbcHyp)
    (d k : ℕ) (R : ℤ[X]) (hR0 : R.eval 0 ≠ 0) (hdeg : k + R.natDegree + 2 ≤ d) :
    ∃ K X : ℕ, ∀ y n : ℕ, 1 ≤ y → n ! ≤ y ^ d →
      (y : ℤ) ^ d + (y : ℤ) ^ k * R.eval (y : ℤ) = (d : ℤ) ^ d * n ! → n ! ≤ K * X ^ n := by sorry
