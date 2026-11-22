-- Prove2me | Theorems.Thm_Egrs75_P4_cond3_of_tail_small
-- name    : Egrs75.P4.cond3_of_tail_small
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T17:27:38.118324+00:00
-- url     : https://prove2.me/theorems/d24b83a3-e0ed-4040-a133-a3bf37ebc3e5
-- title:
--   P4: cond3 of tail small
-- statement:
--   **CONDITION (3), algebraic form (KERNEL-CLEAN).**  For odd `p, q ≥ 3`, given the EGRS
--   tail squeeze in the equality case `A = (p-1)/2`, `B = (q-1)/2`:
--
--     * `hlo : (q-1)/2 * geomQ q i + 1 ≤ T`   (paper: `T ≥ B(q^i-1)/(q-1) + 1`), and
--     * `hTS : T < (p^m + 1)/2`               (paper: `T < S`, equality case `S = (p^m+1)/2`),
--
--   condition (3) reduces to `q^i < p^m`.
--
--   Proof.  `p, q` odd ⟹ `2·((q-1)/2) = q-1` and `2·((p^m+1)/2) = p^m+1`.  From `hTS`,
--   `2T < p^m + 1`, so `2T ≤ p^m`.  From `hlo`, `2·((q-1)/2·G i + 1) ≤ 2T`, i.e.
--   `(q-1)·G i + 2 ≤ 2T ≤ p^m`.  The golden identity `(q-1)·G i = q^i - 1` then gives
--   `(q^i - 1) + 2 ≤ p^m`, i.e. `q^i + 1 ≤ p^m`, hence `q^i < p^m`.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/Egrs75/ConditionThreeWindow.lean#L117-L147
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/Egrs75/ConditionThreeWindow.lean#L117-L147

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

theorem Egrs75.P4.cond3_of_tail_small {p q : ℕ} (hq : 3 ≤ q)
    (hpo : Odd p) (hqo : Odd q) (m i T : ℕ)
    (hlo : (q - 1) / 2 * geomQ q i + 1 ≤ T)
    (hTS : T < (p ^ m + 1) / 2) :
    q ^ i < p ^ m := by sorry
