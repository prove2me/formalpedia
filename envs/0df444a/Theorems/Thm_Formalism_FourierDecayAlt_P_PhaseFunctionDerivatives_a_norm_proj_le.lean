-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_PhaseFunctionDerivatives_a_norm_proj_le
-- name    : Formalism.FourierDecayAlt.P.PhaseFunctionDerivatives.a_norm_proj_le
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T20:30:02.709183+00:00
-- url     : https://prove2.me/theorems/024ecb08-37e2-4810-98b1-278fb0636525
-- title:
--   Phase Function Derivatives: a norm proj le
-- statement:
--   The Phase Function Derivatives construction uses the a norm proj le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/PhaseFunctionDerivatives.lean#L29-L32
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/PhaseFunctionDerivatives.lean#L29-L32

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

theorem Formalism.FourierDecayAlt.P.PhaseFunctionDerivatives.a_norm_proj_le {n : ℕ} (k : Fin n) :
    ‖(ContinuousLinearMap.proj k : (Fin n → ℂ) →L[ℂ] ℂ)‖ ≤ 1 := by sorry
