-- Prove2me | Theorems.Thm_BSLambda_IsTournament_arc_asymm
-- name    : BSLambda.IsTournament.arc_asymm
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T00:48:11.166592+00:00
-- url     : https://prove2.me/theorems/dc302551-6918-4311-8f19-b4e4bab2bc50
-- title:
--   Is Tournament: arc asymm
-- statement:
--   The arc relation of a tournament is asymmetric.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BlockSpectralSensitivity/Defs/Tournament.lean#L79-L80
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BlockSpectralSensitivity/Defs/Tournament.lean#L79-L80

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

theorem BSLambda.IsTournament.arc_asymm (hij : Arc i j) : ¬ Arc j i := by sorry
