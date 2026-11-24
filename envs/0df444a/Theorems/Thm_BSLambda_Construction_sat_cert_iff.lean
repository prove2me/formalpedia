-- Prove2me | Theorems.Thm_BSLambda_Construction_sat_cert_iff
-- name    : BSLambda.Construction.sat_cert_iff
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T00:48:42.603956+00:00
-- url     : https://prove2.me/theorems/e3e5c33c-5a32-48bb-bd48-b10ec60e6bb0
-- title:
--   Construction: sat cert iff
-- statement:
--   Membership in the certificate subcube `C_i`, spelled out (Section 3.2).
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BlockSpectralSensitivity/Construction/Basic.lean#L136-L147
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BlockSpectralSensitivity/Construction/Basic.lean#L136-L147

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

theorem BSLambda.Construction.sat_cert_iff {x : Input (Coord ι r)} :
    (cert Arc γ i).Sat x ↔
      (∀ a : Fin r, x (i, a) = true) ∧
        ∀ j, j ≠ i → Arc i j → x (gateCoord γ i j) = false := by sorry
