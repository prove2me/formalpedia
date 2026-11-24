-- Prove2me | Theorems.Thm_FockSPR_rotational_averaging_bound
-- name    : FockSPR.rotational_averaging_bound
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T02:04:53.75429+00:00
-- url     : https://prove2.me/theorems/2cb4f9db-813c-481a-aacc-eb4e5fe7210e
-- title:
--   Fock SPR: rotational averaging bound
-- statement:
--   The Fock SPR construction uses the rotational averaging bound property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PhaseRetrieval/Constant/Internal/RotationalAveraging.lean#L141-L186
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PhaseRetrieval/Constant/Internal/RotationalAveraging.lean#L141-L186

module
public import Definitions.Def_LeanPool_PhaseRetrieval_Constant_Internal_Definitions
public import Definitions.Def_LeanPool_PhaseRetrieval_Constant_Internal_RotationalAveraging
set_option autoImplicit true
@[expose] public section
public section
open MeasureTheory Real Complex Finset
noncomputable section
open FockSPR

theorem FockSPR.rotational_averaging_bound {r : ℝ} (hr : 0 ≤ r) :
    ∫ t : AddCircle T, (rho (↑r * (fourier 1 t : ℂ))) ^ 2 ∂AddCircle.haarAddCircle ≥
      r ^ 2 / 8 := by sorry
