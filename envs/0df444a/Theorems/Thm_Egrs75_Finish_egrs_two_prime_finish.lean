-- Prove2me | Theorems.Thm_Egrs75_Finish_egrs_two_prime_finish
-- name    : Egrs75.Finish.egrs_two_prime_finish
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T17:31:36.698351+00:00
-- url     : https://prove2.me/theorems/54e81d17-58f6-4536-99bb-10369f7c6f67
-- title:
--   Finish: egrs two prime finish
-- statement:
--   **EGRS75 two-prime theorem — FINISH route.**  For distinct odd primes `p q`, there
--   are infinitely many `n` with `p ∤ C(2n,n)` and `q ∤ C(2n,n)`.
--
--   Assembled through the lex measure: `align_finish` (lex induction, single
--   `egrs_clearing` `sorry`) → `align_to_crux` (clean) → `egrs_two_prime_of_crux` (clean,
--   `EgrsAll`).  Inherits EXACTLY the one `egrs_clearing` `sorryAx` — the EGRS75
--   condition-(3) carry-control residual — under the CORRECT lex interface (no false
--   count-drop hidden).  No `native_decide`, no extra axioms.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/Egrs75/BadPrefixRoute.lean#L435-L439
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/Egrs75/BadPrefixRoute.lean#L435-L439

module
public import Definitions.Def_LeanPool_Egrs75_DigitVector
public import Definitions.Def_LeanPool_Egrs75_DigitAtToolkit
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Definitions.Def_LeanPool_Egrs75_ClearingHigh
public import Definitions.Def_LeanPool_Egrs75_MuFinish
public import Definitions.Def_LeanPool_Egrs75_Reduction
public import Mathlib.Algebra.Order.Ring.GeomSum
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Data.List.GetD
public import Mathlib.Data.Nat.Digits.Lemmas
public import Mathlib.Data.Nat.Totient
public import Definitions.Def_LeanPool_Egrs75_BadPrefixRoute
set_option autoImplicit true
@[expose] public section
public section
open Egrs75 Egrs75.Finish
open Nat
open Finset
open Egrs75
open Egrs75.LeafInduction
open Egrs75.RepairDV
open Egrs75.RepairPaperfaithful
open Egrs75.Probe

theorem Egrs75.Finish.egrs_two_prime_finish {p q : ℕ} (hp : p.Prime) (hq : q.Prime)
    (hpo : Odd p) (hqo : Odd q) (hpq : p ≠ q) :
    {n : ℕ | ¬ p ∣ Nat.centralBinom n ∧ ¬ q ∣ Nat.centralBinom n}.Infinite := by sorry
