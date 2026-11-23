-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_HLsc_normSq_prod
-- name    : Formalism.FourierDecayAlt.P.HLsc.normSq_prod
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T20:09:03.265805+00:00
-- url     : https://prove2.me/theorems/f2010f73-1383-4529-a2f3-830fa37d4e4e
-- title:
--   HLsc: norm Sq prod
-- statement:
--   The HLsc construction uses the norm Sq prod property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/HerglotzLowerSemicontinuous.lean#L311-L316
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/HerglotzLowerSemicontinuous.lean#L311-L316

import Definitions.Def_Formalism_HermitianCurvature_StatementE
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_Herglotz
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_HerglotzLowerSemicontinuous
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.HLsc
open Real Filter Topology Finset MeasureTheory Formalism.FourierDecayAlt.P.Herglotz
variable {d : ℕ}

theorem Formalism.FourierDecayAlt.P.HLsc.normSq_prod (n : ℕ) (y : Fin d → ℝ) :
    ‖∏ j, (1 + Complex.exp (2 * π * Complex.I * (y j : ℂ))) ^ n‖ ^ 2 = pk y ^ n := by sorry
