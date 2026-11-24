-- Prove2me | Theorems.Thm_BSLambda_adj_comp_mulVec_apply
-- name    : BSLambda.adj_comp_mulVec_apply
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T01:16:23.837467+00:00
-- url     : https://prove2.me/theorems/36058f33-9d36-4f3a-9bfc-65adb2b0a26c
-- title:
--   BSLambda: adj comp mul Vec apply
-- statement:
--   **Master identity.**  `A_{f∘g}` acts on a vector by applying `A_g` inside each block and
--   weighting the blocks by the entries of `A_f` at the top bits.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BlockSpectralSensitivity/Spectral/Multiplicative.lean#L227-L236
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BlockSpectralSensitivity/Spectral/Multiplicative.lean#L227-L236

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

theorem BSLambda.adj_comp_mulVec_apply (f : Input W → Bool) (g : Input V → Bool)
    (ψ : Input (W × V) → ℝ) (x : Input (W × V)) :
    (adj (comp f g) *ᵥ ψ) x
      = ∑ w : W, adj f (topBits g x) (flipSet (topBits g x) {w})
          * (adj g *ᵥ fun z ↦ ψ (setBlk x w z)) (blk x w) := by sorry
