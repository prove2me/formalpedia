-- Prove2me | Theorems.Thm_BSLambda_IsTournament_arc_of_not_arc
-- name    : BSLambda.IsTournament.arc_of_not_arc
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T00:48:21.663566+00:00
-- url     : https://prove2.me/theorems/4f66d526-47a8-455d-8bfe-2a6440f217bd
-- title:
--   Is Tournament: arc of not arc
-- statement:
--   The `Bool`-equation form of `BSLambda.IsTournament.arc_or_arc`: if `j` does not beat `i`
--   then `i` beats `j`.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BlockSpectralSensitivity/Defs/Tournament.lean#L88-L89
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BlockSpectralSensitivity/Defs/Tournament.lean#L88-L89

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

theorem BSLambda.IsTournament.arc_of_not_arc (hij : i ≠ j) (hji : Arc j i = false) : Arc i j := by sorry
