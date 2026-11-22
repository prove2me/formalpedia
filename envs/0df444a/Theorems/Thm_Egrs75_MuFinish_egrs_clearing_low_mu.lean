-- Prove2me | Theorems.Thm_Egrs75_MuFinish_egrs_clearing_low_mu
-- name    : Egrs75.MuFinish.egrs_clearing_low_mu
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T17:29:20.662242+00:00
-- url     : https://prove2.me/theorems/8444c6ac-790b-4eee-a2ec-e0b89c3fdb44
-- title:
--   Mu Finish: egrs clearing low mu
-- statement:
--   **The 2026-06-08 residual, discharged.**  Statement byte-identical to
--   `Finish.egrs_clearing_low` (EgrsFinish_core.lean:301): from the μ-closure, a
--   fully `(q,B)`-good number above any floor exists, which clears every index.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/Egrs75/MuFinish.lean#L460-L470
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/Egrs75/MuFinish.lean#L460-L470

module
public import Definitions.Def_LeanPool_Egrs75_DigitAtToolkit
public import Definitions.Def_LeanPool_Egrs75_ConditionThreeWindow
public import Definitions.Def_LeanPool_Egrs75_AddBranch
public import Definitions.Def_LeanPool_Egrs75_MoveDigits
public import Definitions.Def_LeanPool_Egrs75_Reduction
public import Definitions.Def_LeanPool_Egrs75_RoundUp
public import Definitions.Def_LeanPool_Egrs75_SeedWindow
public import Definitions.Def_LeanPool_Egrs75_SubtractBranch
public import Mathlib.Data.Nat.Totient
public import Definitions.Def_LeanPool_Egrs75_MuFinish
set_option autoImplicit true
@[expose] public section
public section
open Egrs75 Egrs75.MuFinish
open Nat
open Egrs75
open Egrs75.LeafInduction
open Egrs75.RepairDV
open Egrs75.RepairPaperfaithful
open Egrs75.P4

theorem Egrs75.MuFinish.egrs_clearing_low_mu {p q : ℕ} (hp : p.Prime) (hq : q.Prime)
    (hpo : Odd p) (hqo : Odd q) (hpq : p ≠ q) (N : ℕ)
    {n : ℕ} (_hpn : LowDigits p n) (_hNn : N < n) (_hbad : 0 < badCountQ q n)
    (_hlow : q ^ (topBadIndex q n) ≤ N) :
    ∃ n', LowDigits p n' ∧ N < n' ∧ (∀ i, topBadIndex q n ≤ i → ¬ BadAt q i n') := by sorry
