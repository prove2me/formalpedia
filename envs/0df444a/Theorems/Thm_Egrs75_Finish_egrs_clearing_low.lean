-- Prove2me | Theorems.Thm_Egrs75_Finish_egrs_clearing_low
-- name    : Egrs75.Finish.egrs_clearing_low
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T17:29:21.010942+00:00
-- url     : https://prove2.me/theorems/5b387e2e-8ce0-4800-8ff0-320c6ea9c017
-- title:
--   Finish: egrs clearing low
-- statement:
--   **THE RESIDUAL, ISOLATED TO THE LOW CASE (one labelled `sorry`): the EGRS75
--   carry-controlled clearing when the top oversized base-`q` index lies *at or below the
--   floor scale*, `q^j ≤ N`.**
--
--   This is the part of the EGRS75 repair Lemma that genuinely needs the base-`q`/base-`p`
--   carry interlock (condition (3), `q^i < p^m`): the complementary case `N < q^j` is
--   discharged kernel-clean below (`Probe.clearing_high`, a fresh window number in
--   `[q^j, 2q^j)` is automatically good at every base-`q` index `≥ j` and exceeds `N`).
--   When `q^j ≤ N` that free window trick is unavailable — the clearing must act on the
--   low base-`q` digits without disturbing the already-small base-`p` block, the SUBTRACT
--   (`N* = N − S`, `S = ((p−A−1)/(p−1))(p^m−1)+1`) / ADD (`N* = N + U`, `U < p^m` via
--   condition (3)) branches of EGRS75 pp.84-85.  Bloom–Croot (arXiv:2509.02835 §1) defer
--   exactly this to [EGRS75]; Mathlib packages neither the elementary carry argument nor
--   the effective equidistribution an analytic proof needs.
--
--   Stated in the same lex coordinates as `egrs_clearing` so the drop stays mechanized
--   (`badPrefix_drop_of_top_cleared`) — no false count-drop is hidden under the sorry.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/Egrs75/BadPrefixRoute.lean#L320-L327
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/Egrs75/BadPrefixRoute.lean#L320-L327

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

theorem Egrs75.Finish.egrs_clearing_low {p q : ℕ} (hp : p.Prime) (hq : q.Prime)
    (hpo : Odd p) (hqo : Odd q) (hpq : p ≠ q) (N : ℕ)
    {n : ℕ} (hpn : LowDigits p n) (hNn : N < n) (hbad : 0 < badCountQ q n)
    (hlow : q ^ (topBadIndex q n) ≤ N) :
    ∃ n', LowDigits p n' ∧ N < n' ∧ (∀ i, topBadIndex q n ≤ i → ¬ BadAt q i n') := by sorry
