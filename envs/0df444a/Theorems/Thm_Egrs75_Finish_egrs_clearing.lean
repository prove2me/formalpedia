-- Prove2me | Theorems.Thm_Egrs75_Finish_egrs_clearing
-- name    : Egrs75.Finish.egrs_clearing
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T17:29:25.174545+00:00
-- url     : https://prove2.me/theorems/b1b9430c-e11a-4692-aa45-0fcc48d50c2a
-- title:
--   Finish: egrs clearing
-- statement:
--   **THE EGRS75 carry-controlled clearing.**
--
--   For distinct odd primes `p q`, a `LowDigits p` number `n` above floor `N` with a top
--   oversized base-`q` digit at `j = topBadIndex q n` admits `n'` that is `LowDigits p`,
--   above `N`, and good at every base-`q` index `≥ j`.  This is the EGRS75 repair Lemma
--   output (`A = (p-1)/2`, `B = (q-1)/2`, side condition at equality, condition (3)
--   `≡ q^i < p^m`).
--
--   Dispatched on the position of the top oversized index relative to the floor scale:
--   * `N < q^j` — KERNEL-CLEAN via `Probe.clearing_high` (a `LowDigits p` window number in
--     `[q^j, 2q^j)` is good at every base-`q` index `≥ j` and exceeds `N`; no carry control).
--   * `q^j ≤ N` — `egrs_clearing_low`, which carries the single labelled `sorry` (the
--     condition-(3) base-`q`/base-`p` carry interlock).
--
--   So `egrs_clearing` inherits EXACTLY the one `egrs_clearing_low` `sorryAx`, now precisely
--   isolated to the low case.  Stated in the lex coordinates so the drop is mechanized
--   (`badPrefix_drop_of_top_cleared`) — no false count-drop is hidden.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/Egrs75/BadPrefixRoute.lean#L346-L357
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/Egrs75/BadPrefixRoute.lean#L346-L357

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

theorem Egrs75.Finish.egrs_clearing {p q : ℕ} (hp : p.Prime) (hq : q.Prime)
    (hpo : Odd p) (hqo : Odd q) (hpq : p ≠ q) (N : ℕ)
    {n : ℕ} (hpn : LowDigits p n) (hNn : N < n) (hbad : 0 < badCountQ q n) :
    ∃ n', LowDigits p n' ∧ N < n' ∧ (∀ i, topBadIndex q n ≤ i → ¬ BadAt q i n') := by sorry
