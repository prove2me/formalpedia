-- Prove2me | Theorems.Thm_BSLambda_Construction_codim_cert
-- name    : BSLambda.Construction.codim_cert
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T00:53:07.700374+00:00
-- url     : https://prove2.me/theorems/4d28abdf-e7f9-4c88-8b3d-524c7742309e
-- title:
--   Construction: codim cert
-- statement:
--   The codimension of every certificate is `r + outdeg(i)` (Section 3.2: `c = r + d`).
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BlockSpectralSensitivity/Construction/Basic.lean#L189-L193
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BlockSpectralSensitivity/Construction/Basic.lean#L189-L193

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

theorem BSLambda.Construction.codim_cert (hT : IsTournament Arc) :
    (cert Arc γ i).codim = r + (outNbrs Arc i).card := by sorry
