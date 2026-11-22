-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_HLsc_fac_eq
-- name    : Formalism.FourierDecayAlt.P.HLsc.fac_eq
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-22T19:49:59.030333+00:00
-- url     : https://prove2.me/theorems/91683988-492e-4cc9-acaf-9b03fd09d6d6
-- title:
--   HLsc: fac eq
-- statement:
--   The HLsc construction uses the fac eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/HerglotzLowerSemicontinuous.lean#L248-L254
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/HerglotzLowerSemicontinuous.lean#L248-L254

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

theorem Formalism.FourierDecayAlt.P.HLsc.fac_eq (t : ℝ) : ‖1 + Complex.exp (2 * π * Complex.I * (t : ℂ))‖ ^ 2 = 2 + 2 * Real.cos (2 * π * t) := by sorry
