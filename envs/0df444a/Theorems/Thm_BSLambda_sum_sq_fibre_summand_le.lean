-- Prove2me | Theorems.Thm_BSLambda_sum_sq_fibre_summand_le
-- name    : BSLambda.sum_sq_fibre_summand_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T01:20:53.789422+00:00
-- url     : https://prove2.me/theorems/7cb0feff-b566-4bdc-ac61-67ebbb59b53c
-- title:
--   BSLambda: sum sq fibre summand le
-- statement:
--   The `w`-th summand of the master identity, restricted to the fibre of `topBits g` over `b`.
--   This is `sum_sq_block_le` with the constant `A_f b b^w` pulled out of the sum.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BlockSpectralSensitivity/Spectral/Multiplicative.lean#L334-L346
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BlockSpectralSensitivity/Spectral/Multiplicative.lean#L334-L346

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

theorem BSLambda.sum_sq_fibre_summand_le (f : Input W → Bool) (g : Input V → Bool)
    (ψ : Input (W × V) → ℝ) (b : Input W) (w : W) :
    ∑ x : Input (W × V), (if topBits g x = b then
        adj f b (flipSet b {w}) * (adj g *ᵥ fun z ↦ ψ (setBlk x w z)) (blk x w) else 0) ^ 2
      ≤ (adj f b (flipSet b {w}) * (lam g * fibreNorm g ψ (flipSet b {w}))) ^ 2 := by sorry
