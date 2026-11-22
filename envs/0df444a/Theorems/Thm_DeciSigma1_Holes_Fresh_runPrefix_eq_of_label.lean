-- Prove2me | Theorems.Thm_DeciSigma1_Holes_Fresh_runPrefix_eq_of_label
-- name    : DeciSigma1.Holes.Fresh.runPrefix_eq_of_label
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T12:54:53.806428+00:00
-- url     : https://prove2.me/theorems/c14e7350-83d8-41f2-ac18-2dae8da49bfc
-- title:
--   Fresh: run Prefix eq of label
-- statement:
--   Equal labels give equal states at the two cuts: the marker texts fix the last
--   `windowLength` letters before each cut, and the second component fixes the state before them.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Holes/Fresh/Deletion.lean#L411-L448
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Holes/Fresh/Deletion.lean#L411-L448

module
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Definitions.Def_LeanPool_DeciSigma1_Holes_Fresh_Parsing
public import Definitions.Def_LeanPool_DeciSigma1_Words_Deletion
public import Mathlib.Data.Finset.Max
public import Definitions.Def_LeanPool_DeciSigma1_Holes_Fresh_Deletion
set_option autoImplicit true
@[expose] public section
public section
open DeciSigma1 DeciSigma1.Holes DeciSigma1.Holes.Fresh
open DeciSigma1.Readers DeciSigma1.Words
open Finset
variable {α : Type} [DecidableEq α] {k : ℕ}
variable {S : Type} [DecidableEq S]
omit [DecidableEq S]

theorem DeciSigma1.Holes.Fresh.runPrefix_eq_of_label (T : Table α S k) {W : Fin k → List α} {t : ℕ} {l : Fin k}
    {c c' : ℕ} (hc : c ≤ (W l).length) (hc' : c' ≤ (W l).length)
    (h : label T W t l c = label T W t l c') : T.runPrefix W l c = T.runPrefix W l c' := by sorry
