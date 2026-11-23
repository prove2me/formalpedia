-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_PhaseFunctionDerivatives_a_norm_inv
-- name    : Formalism.FourierDecayAlt.P.PhaseFunctionDerivatives.a_norm_inv
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T20:30:11.831806+00:00
-- url     : https://prove2.me/theorems/fe7dd2e2-1db5-499c-8faa-dcd3188aba4c
-- title:
--   Phase Function Derivatives: a norm inv
-- statement:
--   The Phase Function Derivatives construction uses the a norm inv property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/PhaseFunctionDerivatives.lean#L40-L58
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/PhaseFunctionDerivatives.lean#L40-L58

import Definitions.Def_Formalism_HermitianCurvature_StatementG
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_PhaseFunctionCriticalPoints
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_OrbitalIntegralConvergesAbs
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_FourierUniquenessMirabolic
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CuspidalIrreducibleSubrep
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_PhaseFunctionDerivatives
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Finset
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.PhaseFunctionDerivatives
open Formalism.FourierDecayAlt.G

theorem Formalism.FourierDecayAlt.P.PhaseFunctionDerivatives.a_norm_inv {n : ℕ} (c : ℕ) (k : Fin n) (x : Fin n → ℂ) (hx : x k ≠ 0) :
    ‖iteratedFDeriv ℂ c (fun y : Fin n → ℂ => (y k)⁻¹) x‖ ≤ c.factorial * (‖x k‖⁻¹ * ‖x k‖⁻¹ ^ c) := by sorry
