-- Prove2me | Theorems.Thm_BSLambda_sum_sq_adj_comp_mulVec_le
-- name    : BSLambda.sum_sq_adj_comp_mulVec_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T01:21:04.495454+00:00
-- url     : https://prove2.me/theorems/97c8dea1-e88e-41f0-a2dc-44596aeb47d4
-- title:
--   BSLambda: sum sq adj comp mul Vec le
-- statement:
--   The operator bound for `A_{f∘g}`, in sum-of-squares form.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BlockSpectralSensitivity/Spectral/Multiplicative.lean#L379-L393
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BlockSpectralSensitivity/Spectral/Multiplicative.lean#L379-L393

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

theorem BSLambda.sum_sq_adj_comp_mulVec_le (f : Input W → Bool) (g : Input V → Bool)
    (ψ : Input (W × V) → ℝ) :
    ∑ x, (adj (comp f g) *ᵥ ψ) x ^ 2 ≤ (lam f * lam g) ^ 2 * ∑ x, ψ x ^ 2 := by sorry
