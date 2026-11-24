-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_JFxG_W_local_zero
-- name    : Formalism.FourierDecayAlt.P.JFxG.W_local_zero
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-24T18:19:30.107585+00:00
-- url     : https://prove2.me/theorems/b81246d4-3ca6-45b8-a150-2d00955514f2
-- title:
--   JFx G: W local zero
-- statement:
--   The JFx G construction uses the W local zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/CompactSupportFiniteClass.lean#L111-L127
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/CompactSupportFiniteClass.lean#L111-L127

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ThetaConjOfParts
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_DilationUnipotentWeylMeasure
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_RegularisedPairingViaPhase
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_NormDiagonalEntryDilationGeneratorLeOne
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CompactSupportFiniteClass
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
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.JFxG
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.JF Formalism.FourierDecayAlt.P.B4
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {k r : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

theorem Formalism.FourierDecayAlt.P.JFxG.W_local_zero {F : Mat k r → E} {V : Set (Mat k r)} (hV : IsOpen V) (h : ∀ x ∈ V, x ∈ GV k r → F x = 0) :
    ∀ (w : List (Bool × Mat k r)), AllLie w → ∀ x ∈ V, x ∈ GV k r → W w F x = 0 := by sorry
