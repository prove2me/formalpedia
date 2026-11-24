-- Prove2me | Theorems.Thm_BSLambda_prod_eigenvector_ne_zero
-- name    : BSLambda.prod_eigenvector_ne_zero
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T01:21:18.879793+00:00
-- url     : https://prove2.me/theorems/453dd3c0-a9c0-48c8-86f9-e6f89c1d85f4
-- title:
--   BSLambda: prod eigenvector ne zero
-- statement:
--   The product eigenvector is nonzero.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BlockSpectralSensitivity/Spectral/Multiplicative.lean#L484-L496
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BlockSpectralSensitivity/Spectral/Multiplicative.lean#L484-L496

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
omit [DecidableEq W] [Fintype V] [DecidableEq V]

theorem BSLambda.prod_eigenvector_ne_zero (g : Input V → Bool) {u : Input V → ℝ} {v : Input W → ℝ}
    (hboth : ∀ β : Bool, ∃ a : Input V, g a = β ∧ u a ≠ 0) (hv : v ≠ 0) :
    (fun x : Input (W × V) ↦ v (topBits g x) * ∏ w, u (blk x w)) ≠ 0 := by sorry
