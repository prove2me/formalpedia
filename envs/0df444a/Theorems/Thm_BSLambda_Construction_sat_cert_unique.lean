-- Prove2me | Theorems.Thm_BSLambda_Construction_sat_cert_unique
-- name    : BSLambda.Construction.sat_cert_unique
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T00:56:43.432396+00:00
-- url     : https://prove2.me/theorems/eded3d70-c46b-4ea0-937c-7f42516f6004
-- title:
--   Construction: sat cert unique
-- statement:
--   Every positive input lies in exactly one certificate subcube: the *owner*
--   (Section 4).
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BlockSpectralSensitivity/Construction/Conflict.lean#L78-L81
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BlockSpectralSensitivity/Construction/Conflict.lean#L78-L81

module
public import Definitions.Def_LeanPool_BlockSpectralSensitivity_Construction_Basic
public import Definitions.Def_LeanPool_BlockSpectralSensitivity_Construction_Conflict
set_option autoImplicit true
@[expose] public section
public section
open BSLambda
open BSLambda.Construction
variable {ι : Type*} {r : ℕ}
variable [DecidableEq ι] {Arc : ι → ι → Bool} {γ : ι → ι → Fin r} {i j : ι}

theorem BSLambda.Construction.sat_cert_unique (hT : IsTournament Arc)
    {x : Input (Coord ι r)} (hi : (cert Arc γ i).Sat x) (hj : (cert Arc γ j).Sat x) :
    i = j := by sorry
