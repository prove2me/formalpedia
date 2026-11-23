-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_PhaseFunctionDerivatives_norm_iteratedFDeriv_inv
-- name    : Formalism.FourierDecayAlt.P.PhaseFunctionDerivatives.norm_iteratedFDeriv_inv
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T20:30:45.660803+00:00
-- url     : https://prove2.me/theorems/27be637a-760f-4da8-9c2f-0dea8bd2711d
-- title:
--   Phase Function Derivatives: norm iterated FDeriv inv
-- statement:
--   The Phase Function Derivatives construction uses the norm iterated FDeriv inv property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/PhaseFunctionDerivatives.lean#L34-L38
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/PhaseFunctionDerivatives.lean#L34-L38

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

theorem Formalism.FourierDecayAlt.P.PhaseFunctionDerivatives.norm_iteratedFDeriv_inv (c : ℕ) (w : ℂ) (hw : w ≠ 0) :
    ‖iteratedFDeriv ℂ c (Inv.inv : ℂ → ℂ) w‖ = c.factorial * (‖w‖⁻¹ * ‖w‖⁻¹ ^ c) := by sorry
