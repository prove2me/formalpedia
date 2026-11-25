-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_JFxDs5_last_level_slice_of_parts
-- name    : Formalism.FourierDecayAlt.P.JFxDs5.last_level_slice_of_parts
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T02:49:02.560056+00:00
-- url     : https://prove2.me/theorems/d76f1a11-8340-4271-adc3-d42f8ea7d364
-- title:
--   JFx Ds5: last level slice of parts
-- statement:
--   The JFx Ds5 construction uses the last level slice of parts property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/LastLevelSliceOfScalar.lean#L72-L74
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/LastLevelSliceOfScalar.lean#L72-L74

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_BesselDomainMeasurable
import Definitions.Def_Formalism_FormalDegreeBessel_FormalDegreeRatio_BFCell
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_LastLevelSliceOfScalar
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix MeasureTheory Filter Topology
open scoped ContDiff
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.JFxDs5
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.JF
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {k : ℕ}

theorem Formalism.FourierDecayAlt.P.JFxDs5.last_level_slice_of_parts : Slice1 → SliceRegularityClauses → Formalism.FourierDecayAlt.JF.LastLevelDiagonalSlice := by sorry
