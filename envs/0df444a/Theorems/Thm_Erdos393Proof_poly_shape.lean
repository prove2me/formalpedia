-- Prove2me | Theorems.Thm_Erdos393Proof_poly_shape
-- name    : Erdos393Proof.poly_shape
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T15:33:08.540932+00:00
-- url     : https://prove2.me/theorems/29f442db-d038-470a-808b-290737371ab6
-- title:
--   Erdos393 Proof: poly shape
-- statement:
--   For a shape `T ∋ 0` with a nonzero element, `y = d·a + ∑ T` satisfies
--   `y^d + y^k R(y) = d^d ∏_{i ∈ T} (a + i)`, with `R(0) ≠ 0` and `k + deg R ≤ d − 2`.
--
--   Source: https://github.com/veljjanoski/erdos393-palomar/blob/ec05768609980a27995453bc1701e6fa3004d675/Solution.lean#L366-L437
-- source:
--   https://github.com/veljjanoski/erdos393-palomar/blob/ec05768609980a27995453bc1701e6fa3004d675/Solution.lean#L366-L437

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

theorem Erdos393Proof.poly_shape (T : Finset ℕ) (h0 : 0 ∈ T) {m : ℕ} (hm : m ∈ T) (hm0 : m ≠ 0) :
    ∃ (k : ℕ) (R : ℤ[X]), R.eval 0 ≠ 0 ∧ k + R.natDegree + 2 ≤ T.card ∧ ∀ a : ℕ,
      ((T.card * a + ∑ i ∈ T, i : ℕ) : ℤ) ^ T.card +
        ((T.card * a + ∑ i ∈ T, i : ℕ) : ℤ) ^ k * R.eval ((T.card * a + ∑ i ∈ T, i : ℕ) : ℤ) =
      (T.card : ℤ) ^ T.card * ((∏ i ∈ T, (a + i) : ℕ) : ℤ) := by sorry
