-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_hessian_at_critical
-- name    : Formalism.FourierDecayAlt.P.hessian_at_critical
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T21:56:10.840486+00:00
-- url     : https://prove2.me/theorems/380e1617-3bc5-4377-ad42-f6b2f1a8cffd
-- title:
--   P: hessian at critical
-- statement:
--   The P construction uses the hessian at critical property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/PhaseFunctionCriticalPoints.lean#L214-L219
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/PhaseFunctionCriticalPoints.lean#L214-L219

import Definitions.Def_Formalism_HermitianCurvature_StatementG
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_PhaseFunctionCriticalPoints
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Finset
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P
open Formalism.FourierDecayAlt.G Formalism.FourierDecayAlt.P.G1

theorem Formalism.FourierDecayAlt.P.hessian_at_critical : Formalism.FourierDecayAlt.G.HessCrit := by sorry
