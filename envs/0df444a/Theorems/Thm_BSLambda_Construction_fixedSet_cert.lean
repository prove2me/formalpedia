-- Prove2me | Theorems.Thm_BSLambda_Construction_fixedSet_cert
-- name    : BSLambda.Construction.fixedSet_cert
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T00:52:56.085775+00:00
-- url     : https://prove2.me/theorems/08a9c33f-2d2a-4ca6-8a7a-32615e7e2303
-- title:
--   Construction: fixed Set cert
-- statement:
--   The set of coordinates fixed by `P_i`: the owner block together with the outgoing
--   gate coordinates (Section 3.2).  No irreflexivity hypothesis is needed; a self-arc `i → i`
--   would just put its gate coordinate in the owner block as well.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BlockSpectralSensitivity/Construction/Basic.lean#L160-L176
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BlockSpectralSensitivity/Construction/Basic.lean#L160-L176

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
variable [Fintype ι] [DecidableEq ι] {Arc : ι → ι → Bool} {γ : ι → ι → Fin r} {i : ι}

theorem BSLambda.Construction.fixedSet_cert :
    (cert Arc γ i).fixedSet = block i ∪ (outNbrs Arc i).image (gateCoord γ i) := by sorry
