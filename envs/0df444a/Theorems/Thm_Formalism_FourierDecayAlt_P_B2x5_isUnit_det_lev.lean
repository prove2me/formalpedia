-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_B2x5_isUnit_det_lev
-- name    : Formalism.FourierDecayAlt.P.B2x5.isUnit_det_lev
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-24T15:58:23.384826+00:00
-- url     : https://prove2.me/theorems/e5cfe6d5-6e6c-4731-8fe2-9cc5f2733181
-- title:
--   B2x5: is Unit det lev
-- statement:
--   The B2x5 construction uses the is Unit det lev property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/HeisenbergLeviConjugationMeasure.lean#L583-L585
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/HeisenbergLeviConjugationMeasure.lean#L583-L585

import Definitions.Def_Formalism_HermitianCurvature_WeylElementCommutesLevelOne
import Definitions.Def_Formalism_FormalDegreeBessel_FinalG
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_HeisenbergLeviConjugationMeasure
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix MeasureTheory Filter Topology
open scoped ComplexConjugate ENNReal NNReal
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.B2x5
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.B2

theorem Formalism.FourierDecayAlt.P.B2x5.isUnit_det_lev {k r' : ℕ} {g : Mat k r'} (hg : IsUnit g.det) : IsUnit (ιLev k 1 r' g).det := by sorry
