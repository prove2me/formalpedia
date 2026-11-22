-- Prove2me | Theorems.Thm_BooleanIsoperimetry_CoherentGap_conwayGuy_block_identity
-- name    : BooleanIsoperimetry.CoherentGap.conwayGuy_block_identity
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T07:22:40.006448+00:00
-- url     : https://prove2.me/theorems/cdad6f3e-f7be-4c3a-bd46-4e79bc579f50
-- title:
--   Coherent Gap: conway Guy block identity
-- statement:
--   The exact triangular-block identity for every Conway--Guy height.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BooleanIsoperimetry/ConwayGuyHeight.lean#L314-L328
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BooleanIsoperimetry/ConwayGuyHeight.lean#L314-L328

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

theorem BooleanIsoperimetry.CoherentGap.conwayGuy_block_identity (dimension : ℕ)
    (hdimension : 2 ≤ dimension) :
    conwayGuyHeight dimension -
          ∑ index : Fin (guide dimension),
            conwayGuyHeight (dimension - index.val - 1) +
        ∑ index : Fin (guide dimension - 1),
          conwayGuyHeight (triangular index.val) = 1 := by sorry
