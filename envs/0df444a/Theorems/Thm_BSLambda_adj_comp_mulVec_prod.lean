-- Prove2me | Theorems.Thm_BSLambda_adj_comp_mulVec_prod
-- name    : BSLambda.adj_comp_mulVec_prod
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T01:21:20.748173+00:00
-- url     : https://prove2.me/theorems/f6a65012-9f1c-417c-9150-61234f05ba47
-- title:
--   BSLambda: adj comp mul Vec prod
-- statement:
--   The product eigenvector: if `u` and `v` are eigenvectors of `A_g` and `A_f` then
--   `x ↦ v (topBits g x) * ∏ w, u (blk x w)` is an eigenvector of `A_{f∘g}`.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BlockSpectralSensitivity/Spectral/Multiplicative.lean#L459-L480
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BlockSpectralSensitivity/Spectral/Multiplicative.lean#L459-L480

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

theorem BSLambda.adj_comp_mulVec_prod (f : Input W → Bool) (g : Input V → Bool) {u : Input V → ℝ}
    {v : Input W → ℝ} (hu : adj g *ᵥ u = lam g • u) (hv : adj f *ᵥ v = lam f • v) :
    adj (comp f g) *ᵥ (fun x ↦ v (topBits g x) * ∏ w, u (blk x w))
      = (lam f * lam g) • fun x ↦ v (topBits g x) * ∏ w, u (blk x w) := by sorry
