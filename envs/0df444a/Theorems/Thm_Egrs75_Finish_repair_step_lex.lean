-- Prove2me | Theorems.Thm_Egrs75_Finish_repair_step_lex
-- name    : Egrs75.Finish.repair_step_lex
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T17:29:27.284903+00:00
-- url     : https://prove2.me/theorems/2ada6d00-fa9f-4762-ba67-f0dd7cdfab39
-- title:
--   Finish: repair step lex
-- statement:
--   **EGRS75 carry-controlled repair step — LEX interface (the architect's NEW step).**
--   For distinct odd primes `p q`, a `LowDigits p` number `n` above floor `N` with an
--   oversized base-`q` digit admits a `LowDigits p` number `n'` above `N` with strictly
--   smaller base-`q` bitmask `badPrefix q n' < badPrefix q n`.
--
--   CRITICAL: there is NO `n < n'` clause (the architectural fix — the paper's SUBTRACT
--   branch legitimately yields `n' < n`); the measure clause is the lex `badPrefix`, NOT
--   `badCountQ`; and `N < n'` threads the magnitude so the final crux gets `n > N`.
--   Assembled kernel-clean from the clearing residual `egrs_clearing` via the proven drop
--   lemma; inherits EXACTLY that one `sorryAx`.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/Egrs75/BadPrefixRoute.lean#L377-L384
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/Egrs75/BadPrefixRoute.lean#L377-L384

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

theorem Egrs75.Finish.repair_step_lex {p q : ℕ} (hp : p.Prime) (hq : q.Prime)
    (hpo : Odd p) (hqo : Odd q) (hpq : p ≠ q) (N : ℕ)
    {n : ℕ} (hpn : LowDigits p n) (hNn : N < n) (hbad : 0 < badCountQ q n) :
    ∃ n', LowDigits p n' ∧ N < n' ∧ badPrefix q n' < badPrefix q n := by sorry
