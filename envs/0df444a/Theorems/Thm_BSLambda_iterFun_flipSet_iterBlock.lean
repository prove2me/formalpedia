-- Prove2me | Theorems.Thm_BSLambda_iterFun_flipSet_iterBlock
-- name    : BSLambda.iterFun_flipSet_iterBlock
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T00:54:49.545597+00:00
-- url     : https://prove2.me/theorems/842c994a-0bc1-44cd-89e1-51f9a4b26a96
-- title:
--   BSLambda: iter Fun flip Set iter Block
-- statement:
--   Flipping the Cartesian-product block `B_{i_1} × ⋯ × B_{i_m}` at the all-zero input
--   turns the value of `F_m` from `0` to `1` (Section 14).
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BlockSpectralSensitivity/Composition.lean#L145-L154
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BlockSpectralSensitivity/Composition.lean#L145-L154

module
public import Definitions.Def_LeanPool_BlockSpectralSensitivity_Defs_Sensitivity
public import Definitions.Def_LeanPool_BlockSpectralSensitivity_Composition
set_option autoImplicit true
@[expose] public section
public section
open BSLambda
open Function
universe u
variable {V ι : Type*} [DecidableEq V] {f : Input V → Bool} {blk : ι → Finset V}

theorem BSLambda.iterFun_flipSet_iterBlock (hzero : f (zeroInput V) = false)
    (hflip : ∀ i, f (flipSet (zeroInput V) (blk i)) = true) :
    ∀ (m : ℕ) (t : IterCoord ι m),
      iterFun f m (flipSet (zeroInput (IterCoord V m)) (iterBlock blk m t)) = true
  := by sorry
