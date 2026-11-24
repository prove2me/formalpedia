-- Prove2me | Theorems.Thm_BSLambda_sum_sq_block_le
-- name    : BSLambda.sum_sq_block_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T01:20:54.537939+00:00
-- url     : https://prove2.me/theorems/aa880f8f-a95b-44a9-9237-ea06d620000b
-- title:
--   BSLambda: sum sq block le
-- statement:
--   Applying `A_g` inside the block `w` and the identity elsewhere is an operator of norm at
--   most `lambda(g)` from the fibre of `topBits g` over `b^w` to the fibre over `b`.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BlockSpectralSensitivity/Spectral/Multiplicative.lean#L290-L330
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BlockSpectralSensitivity/Spectral/Multiplicative.lean#L290-L330

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

theorem BSLambda.sum_sq_block_le (g : Input V → Bool) (ψ : Input (W × V) → ℝ) (b : Input W) (w : W) :
    ∑ x : Input (W × V),
        (if topBits g x = b then (adj g *ᵥ fun z ↦ ψ (setBlk x w z)) (blk x w) else 0) ^ 2
      ≤ lam g ^ 2 * fibreNorm g ψ (flipSet b {w}) ^ 2 := by sorry
