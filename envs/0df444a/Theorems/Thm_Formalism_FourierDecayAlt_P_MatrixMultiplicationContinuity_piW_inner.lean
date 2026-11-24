-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_MatrixMultiplicationContinuity_piW_inner
-- name    : Formalism.FourierDecayAlt.P.MatrixMultiplicationContinuity.piW_inner
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-24T15:50:07.870182+00:00
-- url     : https://prove2.me/theorems/64be9c08-b07a-4922-8484-ac24c654367b
-- title:
--   Matrix Multiplication Continuity: pi W inner
-- statement:
--   The Matrix Multiplication Continuity construction uses the pi W inner property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/ContinuousMulMt.lean#L235-L250
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/ContinuousMulMt.lean#L235-L250

import Definitions.Def_Formalism_HermitianCurvature_BesselNonvanishingReduction
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_HighestWeightUniqueness_FrameInvMulVecNegativeVector
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_BesselNeZeroOfCyclicOrbit
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ContinuousMulMt
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
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.MatrixMultiplicationContinuity
variable {k r : ℕ} {Wp : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]

theorem Formalism.FourierDecayAlt.P.MatrixMultiplicationContinuity.piW_inner {z : Fin (2 * r + k + 1) → ℂ} {u : Fin k → ℝ} {π : Formalism.FourierDecayAlt.ThreeDimData.Mx k r → (Wp →L[ℂ] Wp)}
    (hT : 0 < Formalism.QuantumDeterminants.Tz k r z) (hπ : PI.UpqRep.IsHCTypeW k r z u π) {h : Formalism.FourierDecayAlt.ThreeDimData.Mx k r}
    (hh : h ∈ Formalism.QuantumDeterminants.UWset k r z) (η w : Wp) : ⟪η, π h w⟫_ℂ = ⟪π h⁻¹ η, w⟫_ℂ := by sorry
