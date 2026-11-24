-- Prove2me | Theorems.Thm_BSLambda_IsTournament_outNbrs_union_inNbrs
-- name    : BSLambda.IsTournament.outNbrs_union_inNbrs
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T00:52:13.89802+00:00
-- url     : https://prove2.me/theorems/775e7755-7e71-4192-a7ac-278fb5609a09
-- title:
--   Is Tournament: out Nbrs union in Nbrs
-- statement:
--   The out- and in-neighbours of `v` are exactly the vertices other than `v`.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BlockSpectralSensitivity/Defs/Tournament.lean#L157-L161
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BlockSpectralSensitivity/Defs/Tournament.lean#L157-L161

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
variable [Fintype ι]
variable [DecidableEq ι]
variable {Arc : ι → ι → Bool} {i j l u v : ι}
open BSLambda.IsTournament
variable (h : IsTournament Arc)
include h

theorem BSLambda.IsTournament.outNbrs_union_inNbrs (v : ι) : outNbrs Arc v ∪ inNbrs Arc v = univ.erase v := by sorry
