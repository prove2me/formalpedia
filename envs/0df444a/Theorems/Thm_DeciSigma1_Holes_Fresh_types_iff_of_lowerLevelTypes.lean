-- Prove2me | Theorems.Thm_DeciSigma1_Holes_Fresh_types_iff_of_lowerLevelTypes
-- name    : DeciSigma1.Holes.Fresh.types_iff_of_lowerLevelTypes
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T13:03:56.499398+00:00
-- url     : https://prove2.me/theorems/d668e8bd-7897-44d9-aa77-63319a4bd4d2
-- title:
--   Fresh: types iff of lower Level Types
-- statement:
--   Equal marker texts in the labels mean that the same markers of levels `1, …, t` end at the
--   two cuts.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Holes/Fresh/Deletion.lean#L393-L406
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Holes/Fresh/Deletion.lean#L393-L406

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

theorem DeciSigma1.Holes.Fresh.types_iff_of_lowerLevelTypes {W : Fin k → List α} {t : ℕ} {u : List α} {c c' : ℕ}
    (h : lowerLevelTypes W t u c = lowerLevelTypes W t u c') {r : ℕ} (hr1 : 1 ≤ r)
        (hr : r ≤ t) {m : Fin k}
    (hm : m ∈ active W r) : marker W r m <:+ u.take c ↔ marker W r m <:+ u.take c' := by sorry
