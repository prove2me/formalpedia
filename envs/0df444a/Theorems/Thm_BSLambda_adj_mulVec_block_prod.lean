-- Prove2me | Theorems.Thm_BSLambda_adj_mulVec_block_prod
-- name    : BSLambda.adj_mulVec_block_prod
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T01:21:13.235794+00:00
-- url     : https://prove2.me/theorems/fa93f394-9e7a-4b5d-9c2c-04baed892884
-- title:
--   BSLambda: adj mul Vec block prod
-- statement:
--   **The block step of the product eigenvector computation.**  Applying `A_g` inside the
--   `w`-th block to `x ↦ v (topBits g x) * ∏ w, u (blk x w)` multiplies it by `lambda(g)` and
--   flips the `w`-th top bit: only blocks `z` adjacent to `blk x w` contribute, and for those the
--   top bits change exactly at `w`.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BlockSpectralSensitivity/Spectral/Multiplicative.lean#L427-L455
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BlockSpectralSensitivity/Spectral/Multiplicative.lean#L427-L455

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

theorem BSLambda.adj_mulVec_block_prod (g : Input V → Bool) {u : Input V → ℝ} (v : Input W → ℝ)
    (hu : adj g *ᵥ u = lam g • u) (x : Input (W × V)) (w : W) :
    (adj g *ᵥ fun z : Input V ↦
        v (topBits g (setBlk x w z)) * ∏ w' : W, u (blk (setBlk x w z) w')) (blk x w)
      = lam g * v (flipSet (topBits g x) {w}) * ∏ w' : W, u (blk x w') := by sorry
