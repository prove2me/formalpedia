-- Prove2me | Theorems.Thm_BSLambda_Final_exists_bs_gt_lam_rpow
-- name    : BSLambda.Final.exists_bs_gt_lam_rpow
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T01:40:44.244288+00:00
-- url     : https://prove2.me/theorems/522e7662-0426-465e-a5c8-d6a3fb374a02
-- title:
--   Final: exists bs gt lam rpow
-- statement:
--   **The headline separation** (Sections 5-12).  There is a total Boolean function `f`
--   with
--
--     `bs(f) > lambda(f) ^ 2.12`.
--
--   Self-composition amplifies the seed separation; `exists_ratio_blowup` below supplies
--   the family of inequalities used to refute `bs(f) = O(lambda(f)^2)`.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BlockSpectralSensitivity/Main.lean#L297-L300
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BlockSpectralSensitivity/Main.lean#L297-L300

module
public import Definitions.Def_LeanPool_BlockSpectralSensitivity_Spectral_CertUnion
public import Definitions.Def_LeanPool_BlockSpectralSensitivity_Paley_Tournament
public import Definitions.Def_LeanPool_BlockSpectralSensitivity_Construction_Conflict
public import Definitions.Def_LeanPool_BlockSpectralSensitivity_Construction_BlockSens
public import Definitions.Def_LeanPool_BlockSpectralSensitivity_LLL_GateExists
public import Definitions.Def_LeanPool_BlockSpectralSensitivity_Spectral_Multiplicative
public import Definitions.Def_LeanPool_BlockSpectralSensitivity_Main
set_option autoImplicit true
@[expose] public section
public section
open BSLambda
open BSLambda.Final
open Construction
variable {γ : Idx → Idx → Fin r}

theorem BSLambda.Final.exists_bs_gt_lam_rpow :
    ∃ f : Input (Coord Idx r) → Bool, lam f ^ (2.12 : ℝ) < (bs f : ℝ) := by sorry
