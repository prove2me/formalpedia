-- Prove2me | Theorems.Thm_BSLambda_IsTournament_ne_of_arc
-- name    : BSLambda.IsTournament.ne_of_arc
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T00:47:37.066049+00:00
-- url     : https://prove2.me/theorems/b9f653ee-5bf7-4454-96aa-b1d70865520e
-- title:
--   Is Tournament: ne of arc
-- statement:
--   The endpoints of an arc are distinct.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BlockSpectralSensitivity/Defs/Tournament.lean#L65-L67
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BlockSpectralSensitivity/Defs/Tournament.lean#L65-L67

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

theorem BSLambda.IsTournament.ne_of_arc (hij : Arc i j) : i ≠ j := by sorry
