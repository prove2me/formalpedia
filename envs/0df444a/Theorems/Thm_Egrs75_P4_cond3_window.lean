-- Prove2me | Theorems.Thm_Egrs75_P4_cond3_window
-- name    : Egrs75.P4.cond3_window
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T17:30:39.950526+00:00
-- url     : https://prove2.me/theorems/29a7180a-90cc-40a5-8402-fcef342c3732
-- title:
--   P4: cond3 window
-- statement:
--   **CONDITION-(3) WINDOW PRODUCER (KERNEL-CLEAN).**  For odd primes `p, q ≥ 3`, a number
--   `n` with a bad base-`q` digit, and the ADD trigger `n % q^i < (p^m + 1)/2` at the least
--   strictly-good index `i = leastGoodAbove`, the clearing index `i` is above the top bad index,
--   strictly good, and satisfies condition (3) `q^i < p^m`.
--
--   This is the producer the ADD branch consumes: `i` is a valid place to add (digit strictly
--   good, above the top bad digit), and `q^i < p^m` guarantees the EGRS density `Fact`
--   (`RoundUp.exists_lowDigits_between` at `x = q^i - T`) yields a correction `< p^m` that is
--   base-`p` safe (via `RepairDV.lowDigits_disjoint_add`).
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/Egrs75/ConditionThreeWindow.lean#L361-L368
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/Egrs75/ConditionThreeWindow.lean#L361-L368

module
public import Definitions.Def_LeanPool_Egrs75_DigitVector
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Order.Interval.Finset.Nat
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Algebra.Ring.GeomSum
public import Definitions.Def_LeanPool_Egrs75_ConditionThreeWindow
set_option autoImplicit true
@[expose] public section
public section
open Egrs75 Egrs75.P4
open Nat
open Finset
open Egrs75
open Egrs75.LeafInduction
open Egrs75.RepairDV

theorem Egrs75.P4.cond3_window {p q : ℕ} (_hp : 3 ≤ p) (hq : 3 ≤ q) (hpo : Odd p) (hqo : Odd q)
    (n m : ℕ) (hbad : 0 < badCountQ q n)
    (hTS : n % q ^ (leastGoodAbove hq hbad) < (p ^ m + 1) / 2) :
    ∃ i, topBadIndex q n < i ∧ n / q ^ i % q < (q - 1) / 2 ∧ q ^ i < p ^ m := by sorry
