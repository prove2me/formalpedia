-- Prove2me | Theorems.Thm_Egrs75_Finish_badPrefix_drop_of_top_cleared
-- name    : Egrs75.Finish.badPrefix_drop_of_top_cleared
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T17:29:21.984483+00:00
-- url     : https://prove2.me/theorems/0b8950be-db52-4025-8366-5dbd55a97325
-- title:
--   Finish: bad Prefix drop of top cleared
-- statement:
--   **The lex-measure drop (KERNEL-CLEAN).**  Let `j = topBadIndex q n` (with `n`
--   having a bad digit).  If `n'` has no bad base-`q` digit at any index `≥ j`, then
--   `badPrefix q n' < badPrefix q n`.
--
--   Proof: all bad indices of `n'` are `< j`, so by `Nat.geomSum_lt`,
--   `badPrefix q n' = ∑_{i ∈ badIndexSet q n'} 2^i < 2^j`; and `2^j ≤ badPrefix q n`
--   since `j` is itself a bad index of `n`.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/Egrs75/BadPrefixRoute.lean#L192-L208
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/Egrs75/BadPrefixRoute.lean#L192-L208

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

theorem Egrs75.Finish.badPrefix_drop_of_top_cleared {q n n' : ℕ} (hq : 1 < q)
    (hbad : 0 < badCountQ q n)
    (hcleared : ∀ i, topBadIndex q n ≤ i → ¬ BadAt q i n') :
    badPrefix q n' < badPrefix q n := by sorry
