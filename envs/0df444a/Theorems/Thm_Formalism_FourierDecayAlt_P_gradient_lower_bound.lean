-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_gradient_lower_bound
-- name    : Formalism.FourierDecayAlt.P.gradient_lower_bound
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T21:56:12.809845+00:00
-- url     : https://prove2.me/theorems/70d9b5aa-8f33-40f8-94fc-4d81ea3a11a9
-- title:
--   P: gradient lower bound
-- statement:
--   The P construction uses the gradient lower bound property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/PhaseFunctionCriticalPoints.lean#L234-L269
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/PhaseFunctionCriticalPoints.lean#L234-L269

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

theorem Formalism.FourierDecayAlt.P.gradient_lower_bound : Formalism.FourierDecayAlt.G.GradLower := by sorry
