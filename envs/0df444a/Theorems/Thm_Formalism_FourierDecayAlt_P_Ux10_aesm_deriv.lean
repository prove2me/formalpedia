-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_Ux10_aesm_deriv
-- name    : Formalism.FourierDecayAlt.P.Ux10.aesm_deriv
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-24T16:11:37.04562+00:00
-- url     : https://prove2.me/theorems/0419bbf0-a38b-42d4-b974-68ebfa9ede85
-- title:
--   Ux10: aesm deriv
-- statement:
--   The Ux10 construction uses the aesm deriv property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/PhiBoundPartsOfRadicalParametrisation.lean#L109-L122
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/PhiBoundPartsOfRadicalParametrisation.lean#L109-L122

import Definitions.Def_Formalism_HermitianCurvature_StatementU
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_DilationUnipotentWeylMeasure
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_BetaSesquilinearity
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_SymmetricScalarBlockMatrixTranspose
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_SymmetricScalarBlockMatrixMul
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_DirectionsInParabolic
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_Block3MulBlocks
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CoordinateSizesOfHypotheses
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_CayleyTransformPreservesForm
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_PhiBoundPartsOfRadicalParametrisation
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix MeasureTheory
open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.U Formalism.REAL Formalism.QuantumDeterminants
open MeasureTheory Filter Topology
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.Ux10
variable {α : Type*} [MeasurableSpace α] {μ : Measure α} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem Formalism.FourierDecayAlt.P.Ux10.aesm_deriv {G : α → ℝ → E} {G' : α → E} (hd : ∀ ξ, HasDerivAt (G ξ) (G' ξ) 0)
    (hm : ∀ᶠ t in 𝓝 (0 : ℝ), AEStronglyMeasurable (fun ξ => G ξ t) μ) : AEStronglyMeasurable G' μ := by sorry
