-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_B4_smooth_on_of_word_derivatives
-- name    : Formalism.FourierDecayAlt.P.B4.smooth_on_of_word_derivatives
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-24T14:25:18.956853+00:00
-- url     : https://prove2.me/theorems/60f0d740-8636-4eda-a73e-0e7cc87a6173
-- title:
--   B4: smooth on of word derivatives
-- statement:
--   The B4 construction uses the smooth on of word derivatives property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/DilationUnipotentWeylMeasure.lean#L458-L475
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/DilationUnipotentWeylMeasure.lean#L458-L475

import Definitions.Def_Formalism_HermitianCurvature_StatementB
import Definitions.Def_Formalism_FormalDegreeBessel_FormalDegreeRatio_UnitaryWeylNormalHolds
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_CartanInvolutionConjTransposeMul
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_DilationUnipotentWeylMeasure
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Filter Topology
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.B4
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {k r : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

theorem Formalism.FourierDecayAlt.P.B4.smooth_on_of_word_derivatives {f : Mat k r → E} (w : List (Bool × Mat k r)) (hw : AllLie w) :
    ∀ m : ℕ, CkOn ((m + w.length : ℕ) : ℕ∞) (GV k r) f → CkOn ((m : ℕ) : ℕ∞) (GV k r) (W w f) := by sorry
