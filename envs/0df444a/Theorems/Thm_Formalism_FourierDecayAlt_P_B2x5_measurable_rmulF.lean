-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_B2x5_measurable_rmulF
-- name    : Formalism.FourierDecayAlt.P.B2x5.measurable_rmulF
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-24T14:56:29.800505+00:00
-- url     : https://prove2.me/theorems/0f8492f2-3794-4dd2-a112-0c51f8b03e9d
-- title:
--   B2x5: measurable rmul F
-- statement:
--   The B2x5 construction uses the measurable rmul F property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/HeisenbergLeviConjugationMeasure.lean#L626-L633
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/HeisenbergLeviConjugationMeasure.lean#L626-L633

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

theorem Formalism.FourierDecayAlt.P.B2x5.measurable_rmulF {n : ℕ} (a : Matrix (Fin n) (Fin n) ℂ) : Measurable (rmulF a) := by sorry
