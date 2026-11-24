-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_JFxB_integral_list_smul
-- name    : Formalism.FourierDecayAlt.P.JFxB.integral_list_smul
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-24T17:25:42.578935+00:00
-- url     : https://prove2.me/theorems/fd16a57c-45d7-4f94-8651-8174c9b66677
-- title:
--   JFx B: integral list smul
-- statement:
--   The JFx B construction uses the integral list smul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/JfCVUnderIntOfParts.lean#L280-L294
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/JfCVUnderIntOfParts.lean#L280-L294

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CvRhoOfParts
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_RegularisedPairingViaPhase
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_JfCVUnderIntOfParts
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
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.JFxB
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.P.BetaSesquilinearity
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {k r : ℕ}

theorem Formalism.FourierDecayAlt.P.JFxB.integral_list_smul {α V : Type*} [MeasurableSpace α] {μ : Measure α} [NormedAddCommGroup V]
    [NormedSpace ℂ V] [CompleteSpace V] {ι : Type*} (l : List ι) (c : ι → ℂ) (φ : ι → α → V)
    (h : ∀ i ∈ l, Integrable (φ i) μ) :
    Integrable (fun p => (l.map fun i => c i • φ i p).sum) μ ∧
      (∫ p, (l.map fun i => c i • φ i p).sum ∂μ) = (l.map fun i => c i • ∫ p, φ i p ∂μ).sum := by sorry
