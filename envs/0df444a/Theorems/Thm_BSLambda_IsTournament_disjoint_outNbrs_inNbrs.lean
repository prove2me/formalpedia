-- Prove2me | Theorems.Thm_BSLambda_IsTournament_disjoint_outNbrs_inNbrs
-- name    : BSLambda.IsTournament.disjoint_outNbrs_inNbrs
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T00:52:10.2059+00:00
-- url     : https://prove2.me/theorems/d19095c5-d3d7-453c-beaf-45a5d407de50
-- title:
--   Is Tournament: disjoint out Nbrs in Nbrs
-- statement:
--   The out-neighbourhood and the in-neighbourhood of a vertex are disjoint.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BlockSpectralSensitivity/Defs/Tournament.lean#L116-L118
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BlockSpectralSensitivity/Defs/Tournament.lean#L116-L118

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
variable {Arc : ι → ι → Bool} {i j : ι}

theorem BSLambda.IsTournament.disjoint_outNbrs_inNbrs (h : IsTournament Arc) (v : ι) :
    Disjoint (outNbrs Arc v) (inNbrs Arc v) := by sorry
