-- Prove2me | Theorems.Thm_BSLambda_LLL_radiusTwoEvent_determined
-- name    : BSLambda.LLL.radiusTwoEvent_determined
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T01:07:15.67099+00:00
-- url     : https://prove2.me/theorems/b311599b-d044-4b81-b794-d8224e3dbfe5
-- title:
--   LLL: radius Two Event determined
-- statement:
--   The radius-two event is determined by the arc variables inside its support.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BlockSpectralSensitivity/LLL/Obstruction.lean#L791-L799
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BlockSpectralSensitivity/LLL/Obstruction.lean#L791-L799

module
public import Definitions.Def_LeanPool_BlockSpectralSensitivity_LLL_Asymmetric
public import Definitions.Def_LeanPool_BlockSpectralSensitivity_Construction_Basic
public import Definitions.Def_LeanPool_BlockSpectralSensitivity_Numerics_Binomial
public import Definitions.Def_LeanPool_BlockSpectralSensitivity_LLL_Obstruction
set_option autoImplicit true
@[expose] public section
public section
open BSLambda
open BSLambda.LLL
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable {r : ℕ}

theorem BSLambda.LLL.radiusTwoEvent_determined {Arc : ι → ι → Bool} (hT : IsTournament Arc)
    (S : Finset ι) :
    Determined (β := fun _ : ι × ι => Fin r) S.offDiag (radiusTwoEvent (r := r) Arc S) := by sorry
