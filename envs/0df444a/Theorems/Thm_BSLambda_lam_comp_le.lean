-- Prove2me | Theorems.Thm_BSLambda_lam_comp_le
-- name    : BSLambda.lam_comp_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T01:21:06.67458+00:00
-- url     : https://prove2.me/theorems/07c0d4e8-ae02-441a-8403-d2b443cb5406
-- title:
--   BSLambda: lam comp le
-- statement:
--   **Submultiplicativity of `lambda`.**
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BlockSpectralSensitivity/Spectral/Multiplicative.lean#L396-L400
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BlockSpectralSensitivity/Spectral/Multiplicative.lean#L396-L400

module
public import Definitions.Def_LeanPool_BlockSpectralSensitivity_Spectral_OpNorm
public import Definitions.Def_LeanPool_BlockSpectralSensitivity_Composition
public import Definitions.Def_LeanPool_BlockSpectralSensitivity_Spectral_Multiplicative
set_option autoImplicit true
@[expose] public section
public section
open BSLambda
open scoped Matrix
variable {W V : Type*} [Fintype W] [DecidableEq W] [Fintype V] [DecidableEq V]

theorem BSLambda.lam_comp_le (f : Input W → Bool) (g : Input V → Bool) :
    lam (comp f g) ≤ lam f * lam g := by sorry
