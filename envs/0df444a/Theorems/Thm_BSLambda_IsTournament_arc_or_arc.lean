-- Prove2me | Theorems.Thm_BSLambda_IsTournament_arc_or_arc
-- name    : BSLambda.IsTournament.arc_or_arc
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T00:48:01.923722+00:00
-- url     : https://prove2.me/theorems/4644bfb4-1833-45cd-b050-169f1b555d7b
-- title:
--   Is Tournament: arc or arc
-- statement:
--   Any two distinct vertices of a tournament are joined by an arc.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BlockSpectralSensitivity/Defs/Tournament.lean#L83-L84
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BlockSpectralSensitivity/Defs/Tournament.lean#L83-L84

module
public import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
public import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
public import Mathlib.Data.Fintype.Card
public import Definitions.Def_LeanPool_BlockSpectralSensitivity_Defs_Tournament
set_option autoImplicit true
@[expose] public section
public section
open BSLambda
open Finset
variable {ι : Type*}
open BSLambda.IsTournament
variable {Arc : ι → ι → Bool} (h : IsTournament Arc) {i j : ι}
include h

theorem BSLambda.IsTournament.arc_or_arc (hij : i ≠ j) : Arc i j ∨ Arc j i := by sorry
