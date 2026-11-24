-- Prove2me | Theorems.Thm_BSLambda_exists_apply_eq_and_ne_zero
-- name    : BSLambda.exists_apply_eq_and_ne_zero
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T01:21:14.757952+00:00
-- url     : https://prove2.me/theorems/0d500580-1ccf-47de-b792-b85ecf0dfb0d
-- title:
--   BSLambda: exists apply eq and ne zero
-- statement:
--   The support of an eigenvector for a nonzero eigenvalue meets both sides of the
--   bipartition.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BlockSpectralSensitivity/Spectral/Multiplicative.lean#L406-L421
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BlockSpectralSensitivity/Spectral/Multiplicative.lean#L406-L421

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

theorem BSLambda.exists_apply_eq_and_ne_zero (g : Input V → Bool) {μ : ℝ} (hμ : μ ≠ 0)
    {u : Input V → ℝ} (hu : u ≠ 0) (hev : adj g *ᵥ u = μ • u) (β : Bool) :
    ∃ a : Input V, g a = β ∧ u a ≠ 0 := by sorry
