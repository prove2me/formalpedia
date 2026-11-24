-- Prove2me | Theorems.Thm_BSLambda_LLL_flagEvent_determined
-- name    : BSLambda.LLL.flagEvent_determined
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T01:06:37.670659+00:00
-- url     : https://prove2.me/theorems/1fc268fd-3db1-4232-9ca7-31f24b15a80f
-- title:
--   LLL: flag Event determined
-- statement:
--   The flag event is determined by the arc variables inside its support.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BlockSpectralSensitivity/LLL/Obstruction.lean#L516-L523
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BlockSpectralSensitivity/LLL/Obstruction.lean#L516-L523

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

theorem BSLambda.LLL.flagEvent_determined {Arc : ι → ι → Bool} (hT : IsTournament Arc)
    {F : Flag1 ι} (hF : F.Active Arc) :
    Determined (β := fun _ : ι × ι => Fin r) F.supp.offDiag
      (flagEvent (r := r) Arc F) := by sorry
