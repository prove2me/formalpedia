-- Prove2me | Theorems.Thm_BSLambda_IsTournament_arc_eq_false_of_arc
-- name    : BSLambda.IsTournament.arc_eq_false_of_arc
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T00:50:26.759079+00:00
-- url     : https://prove2.me/theorems/291d056a-cfdf-40a9-a90d-d6e862bc5f75
-- title:
--   Is Tournament: arc eq false of arc
-- statement:
--   Asymmetry in the `Bool`-equation form consumed by the certificate-conflict lemmas:
--   an arc `i → j` forces `Arc j i = false`.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BlockSpectralSensitivity/Defs/Tournament.lean#L75-L76
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BlockSpectralSensitivity/Defs/Tournament.lean#L75-L76

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

theorem BSLambda.IsTournament.arc_eq_false_of_arc (hij : Arc i j) : Arc j i = false := by sorry
