-- Prove2me | Theorems.Thm_Egrs75_MuFinish_muVal_lt_of
-- name    : Egrs75.MuFinish.muVal_lt_of
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T17:29:13.626344+00:00
-- url     : https://prove2.me/theorems/f2165233-853a-4018-a07e-087fc120386a
-- title:
--   Mu Finish: mu Val lt of
-- statement:
--   **μ strictly drops.**  `μ(n') < μ(n)` whenever `n'` is fully good, or its
--   working index dropped, or the index held and the digit there strictly climbed.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/Egrs75/MuFinish.lean#L93-L127
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/Egrs75/MuFinish.lean#L93-L127

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

theorem Egrs75.MuFinish.muVal_lt_of {q : ℕ} (hq3 : 3 ≤ q) {n n' : ℕ} (hbad : 0 < badCountQ q n)
    (h : badCountQ q n' = 0 ∨
         ∃ hbad' : 0 < badCountQ q n',
           leastGoodAbove hq3 hbad' < leastGoodAbove hq3 hbad ∨
           (leastGoodAbove hq3 hbad' = leastGoodAbove hq3 hbad ∧
            n / q ^ (leastGoodAbove hq3 hbad) % q
              < n' / q ^ (leastGoodAbove hq3 hbad') % q)) :
    muVal q hq3 n' < muVal q hq3 n := by sorry
