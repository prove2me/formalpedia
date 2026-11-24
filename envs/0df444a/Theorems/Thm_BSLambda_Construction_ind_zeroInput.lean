-- Prove2me | Theorems.Thm_BSLambda_Construction_ind_zeroInput
-- name    : BSLambda.Construction.ind_zeroInput
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T00:50:55.865806+00:00
-- url     : https://prove2.me/theorems/691a2fb3-4504-43b2-8422-75edbee67db8
-- title:
--   Construction: ind zero Input
-- statement:
--   `f (0^V) = 0`: no certificate is satisfied by the all-zero input, because every
--   certificate requires its whole (nonempty) owner block to be `1` (Section 5).
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BlockSpectralSensitivity/Construction/BlockSens.lean#L37-L39
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BlockSpectralSensitivity/Construction/BlockSens.lean#L37-L39

module
public import Definitions.Def_LeanPool_BlockSpectralSensitivity_Construction_Basic
public import Definitions.Def_LeanPool_BlockSpectralSensitivity_Construction_BlockSens
set_option autoImplicit true
@[expose] public section
public section
open BSLambda
open BSLambda.Construction
variable {ι : Type*} {r : ℕ}

theorem BSLambda.Construction.ind_zeroInput [Fintype ι] [DecidableEq ι] [NeZero r] (Arc : ι → ι → Bool)
    (γ : ι → ι → Fin r) : ind Arc γ (zeroInput (Coord ι r)) = false := by sorry
