-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_MatrixMultiplicationContinuity_aesm_of_contOn
-- name    : Formalism.FourierDecayAlt.P.MatrixMultiplicationContinuity.aesm_of_contOn
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T04:01:18.742279+00:00
-- url     : https://prove2.me/theorems/b990f0c6-56b5-44fd-a69b-67d7c6469651
-- title:
--   Matrix Multiplication Continuity: aesm of cont On
-- statement:
--   The Matrix Multiplication Continuity construction uses the aesm of cont On property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/ReproducingFormulaReduction.lean#L53-L58
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/ReproducingFormulaReduction.lean#L53-L58

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ContinuousMulMt
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_UhMeasurableSet
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_SigmaContOn
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ReproducingFormulaReduction
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Matrix
open scoped InnerProductSpace ENNReal
noncomputable section
set_option maxHeartbeats 1600000
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.MatrixMultiplicationContinuity
open Formalism.FourierDecayAlt.ThreeDimData
variable {k r : ℕ}

theorem Formalism.FourierDecayAlt.P.MatrixMultiplicationContinuity.aesm_of_contOn {α E : Type*} [TopologicalSpace α] [MeasurableSpace α] [OpensMeasurableSpace α]
    [SecondCountableTopology α] [NormedAddCommGroup E] [SecondCountableTopology E]
    {μ : Measure α} {f : α → E} {s : Set α} (hf : ContinuousOn f s) (hs : MeasurableSet s)
    (hμ : ∀ᵐ x ∂μ, x ∈ s) : AEStronglyMeasurable f μ := by sorry
