-- Prove2me | Theorems.Thm_BooleanIsoperimetry_CoherentGap_conwayGuyDifference_succ
-- name    : BooleanIsoperimetry.CoherentGap.conwayGuyDifference_succ
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T07:17:31.018842+00:00
-- url     : https://prove2.me/theorems/3efe4136-b767-4fb2-84d7-faa38c64a688
-- title:
--   Coherent Gap: conway Guy Difference succ
-- statement:
--   The Coherent Gap construction uses the conway Guy Difference succ property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BooleanIsoperimetry/ConwayGuyHeight.lean#L74-L78
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BooleanIsoperimetry/ConwayGuyHeight.lean#L74-L78

module
public import Definitions.Def_LeanPool_BooleanIsoperimetry_ConwayGuyCoherentGap
public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Data.Rat.Cast.Order
public import Mathlib.Tactic.Linarith.Frontend
public import Mathlib.Tactic.NormNum.Abs
public import Mathlib.Tactic.NormNum.DivMod
public import Mathlib.Tactic.NormNum.OfScientific
public import Mathlib.Tactic.Ring.RingNF
public import Definitions.Def_LeanPool_BooleanIsoperimetry_ConwayGuyHeight
set_option autoImplicit true
@[expose] public section
public section
open scoped BigOperators
open BooleanIsoperimetry BooleanIsoperimetry.CoherentGap

theorem BooleanIsoperimetry.CoherentGap.conwayGuyDifference_succ (index : ℕ) :
    conwayGuyDifference (index + 1) =
      ∑ offset ∈ Finset.range (guide (index + 2)),
        conwayGuyDifference (index - offset) := by sorry
