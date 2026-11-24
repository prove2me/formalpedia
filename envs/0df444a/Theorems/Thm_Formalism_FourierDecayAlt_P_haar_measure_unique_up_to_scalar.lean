-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_haar_measure_unique_up_to_scalar
-- name    : Formalism.FourierDecayAlt.P.haar_measure_unique_up_to_scalar
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-24T15:26:04.010162+00:00
-- url     : https://prove2.me/theorems/ae6823a9-44ac-4d40-9ca9-d82822c51285
-- title:
--   P: haar measure unique up to scalar
-- statement:
--   The P construction uses the haar measure unique up to scalar property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/ConjugationContinuousOnInvertible.lean#L271-L271
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/ConjugationContinuousOnInvertible.lean#L271-L271

import Definitions.Def_Formalism_HermitianCurvature_WeylElementCommutesLevelOne
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_BlochKatoDuality
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ConjugationContinuousOnInvertible
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix MeasureTheory Filter Topology
open scoped ENNReal NNReal
open Formalism.FourierDecayAlt.B2 Formalism.FourierDecayAlt.B Formalism.QuantumDeterminants Formalism.REAL
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P

theorem Formalism.FourierDecayAlt.P.haar_measure_unique_up_to_scalar : Formalism.FourierDecayAlt.B2.HaarUnique := by sorry
