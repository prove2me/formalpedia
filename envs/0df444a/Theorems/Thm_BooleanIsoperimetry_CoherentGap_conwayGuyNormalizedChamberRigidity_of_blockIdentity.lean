-- Prove2me | Theorems.Thm_BooleanIsoperimetry_CoherentGap_conwayGuyNormalizedChamberRigidity_of_blockIdentity
-- name    : BooleanIsoperimetry.CoherentGap.conwayGuyNormalizedChamberRigidity_of_blockIdentity
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T07:33:04.06611+00:00
-- url     : https://prove2.me/theorems/e252ee05-4036-44f0-97be-4c9a3568376b
-- title:
--   Coherent Gap: conway Guy Normalized Chamber Rigidity of block Identity
-- statement:
--   Conditional concrete normalized chamber rigidity.  The height file
--   discharges `hblock` from the published Conway--Guy recurrence.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BooleanIsoperimetry/ConwayGuyRigidity.lean#L78-L88
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BooleanIsoperimetry/ConwayGuyRigidity.lean#L78-L88

module
public import Definitions.Def_LeanPool_BooleanIsoperimetry_ConwayGuyCoherentGap
public import Definitions.Def_LeanPool_BooleanIsoperimetry_ConwayGuyHeight
public import Mathlib.Data.Rat.Cast.Order
public import Mathlib.Tactic.NormNum.Abs
public import Mathlib.Tactic.NormNum.DivMod
public import Mathlib.Tactic.NormNum.OfScientific
public import Mathlib.Tactic.NormNum.Pow
public import Definitions.Def_LeanPool_BooleanIsoperimetry_ConwayGuyRigidity
set_option autoImplicit true
@[expose] public section
public section
open BooleanIsoperimetry BooleanIsoperimetry.CoherentGap

theorem BooleanIsoperimetry.CoherentGap.conwayGuyNormalizedChamberRigidity_of_blockIdentity
    (hblock : ∀ offset, ConwayGuyBlockIdentity offset) {n : ℕ}
    (candidate : Fin n → ℝ)
    (hgap : ∀ relation,
      IsLiftableUnit (conwayGuyArithmetic.tower.weights n) relation →
        1 ≤ realDot relation candidate) :
    ∀ coordinate,
      (conwayGuyArithmetic.tower.weights n coordinate : ℝ) ≤
        candidate coordinate := by sorry
