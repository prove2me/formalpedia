-- Prove2me | Theorems.Thm_Erdos393Proof_shape_bound
-- name    : Erdos393Proof.shape_bound
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T15:32:37.991515+00:00
-- url     : https://prove2.me/theorems/90c0cee6-3dfa-55f0-bec8-99f09eddc6ac
-- title:
--   Erdos393 Proof: shape bound
-- statement:
--   One shape `T` gives `n!` at most an exponential in `n`.
--
--   Source: https://github.com/veljjanoski/erdos393-palomar/blob/ec05768609980a27995453bc1701e6fa3004d675/Solution.lean#L440-L455
-- source:
--   https://github.com/veljjanoski/erdos393-palomar/blob/ec05768609980a27995453bc1701e6fa3004d675/Solution.lean#L440-L455

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

theorem Erdos393Proof.shape_bound (habc : AbcHyp)
    (T : Finset ℕ) (h0 : 0 ∈ T) {m : ℕ} (hm : m ∈ T) (hm0 : m ≠ 0) :
    ∃ K X : ℕ, ∀ a n : ℕ, ∏ i ∈ T, (a + i) = n ! → n ! ≤ K * X ^ n := by sorry
