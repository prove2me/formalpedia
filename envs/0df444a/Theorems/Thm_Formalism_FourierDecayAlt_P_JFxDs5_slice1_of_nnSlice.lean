-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_JFxDs5_slice1_of_nnSlice
-- name    : Formalism.FourierDecayAlt.P.JFxDs5.slice1_of_nnSlice
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T02:47:01.074834+00:00
-- url     : https://prove2.me/theorems/bf7e249b-18da-41ee-846e-47115702781c
-- title:
--   JFx Ds5: slice1 of nn Slice
-- statement:
--   The JFx Ds5 construction uses the slice1 of nn Slice property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/LastLevelSliceOfScalar.lean#L76-L115
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/LastLevelSliceOfScalar.lean#L76-L115

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

theorem Formalism.FourierDecayAlt.P.JFxDs5.slice1_of_nnSlice : NNSlice → Slice1 := by sorry
