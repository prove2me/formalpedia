-- Prove2me | Theorems.Thm_BSLambda_card_iterCoord
-- name    : BSLambda.card_iterCoord
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T00:54:48.594873+00:00
-- url     : https://prove2.me/theorems/53a2ce19-5960-4033-a5c4-a48f02d53cdb
-- title:
--   BSLambda: card iter Coord
-- statement:
--   There are exactly `k^m` tuples, where `k = #V` (Section 14).
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BlockSpectralSensitivity/Composition.lean#L72-L77
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BlockSpectralSensitivity/Composition.lean#L72-L77

module
public import Definitions.Def_LeanPool_BlockSpectralSensitivity_Defs_Sensitivity
public import Definitions.Def_LeanPool_BlockSpectralSensitivity_Composition
set_option autoImplicit true
@[expose] public section
public section
open BSLambda
open Function
universe u

theorem BSLambda.card_iterCoord (V : Type*) [Fintype V] :
    ∀ m, Fintype.card (IterCoord V m) = Fintype.card V ^ m
  := by sorry
