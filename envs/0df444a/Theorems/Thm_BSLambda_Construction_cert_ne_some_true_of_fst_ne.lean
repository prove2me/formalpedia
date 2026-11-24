-- Prove2me | Theorems.Thm_BSLambda_Construction_cert_ne_some_true_of_fst_ne
-- name    : BSLambda.Construction.cert_ne_some_true_of_fst_ne
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T00:52:52.777807+00:00
-- url     : https://prove2.me/theorems/d6786789-c6a2-47be-ab3a-856add24760b
-- title:
--   Construction: cert ne some true of fst ne
-- statement:
--   `P_i` never fixes a coordinate outside `B_i` to `true`.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BlockSpectralSensitivity/Construction/Basic.lean#L125-L126
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BlockSpectralSensitivity/Construction/Basic.lean#L125-L126

module
public import Definitions.Def_LeanPool_BlockSpectralSensitivity_Defs_Sensitivity
public import Definitions.Def_LeanPool_BlockSpectralSensitivity_Defs_Subcube
public import Definitions.Def_LeanPool_BlockSpectralSensitivity_Defs_Tournament
public import Definitions.Def_LeanPool_BlockSpectralSensitivity_Construction_Basic
set_option autoImplicit true
@[expose] public section
public section
open BSLambda
open BSLambda.Construction
variable {ι : Type*} {r : ℕ}
variable [DecidableEq ι]
variable {Arc : ι → ι → Bool} {γ : ι → ι → Fin r} {i j : ι} {v : Coord ι r} {b : Bool}

theorem BSLambda.Construction.cert_ne_some_true_of_fst_ne (h : v.1 ≠ i) : cert Arc γ i v ≠ some true := by sorry
