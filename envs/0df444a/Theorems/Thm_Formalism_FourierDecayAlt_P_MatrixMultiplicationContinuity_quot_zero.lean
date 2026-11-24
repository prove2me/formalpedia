-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_MatrixMultiplicationContinuity_quot_zero
-- name    : Formalism.FourierDecayAlt.P.MatrixMultiplicationContinuity.quot_zero
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-24T16:18:02.300446+00:00
-- url     : https://prove2.me/theorems/cec5f2db-5ede-4a43-9a97-03d9d5979be9
-- title:
--   Matrix Multiplication Continuity: quot zero
-- statement:
--   The Matrix Multiplication Continuity construction uses the quot zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/ContinuousMulMt.lean#L72-L109
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/ContinuousMulMt.lean#L72-L109

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
set_option maxHeartbeats 800000

theorem Formalism.FourierDecayAlt.P.MatrixMultiplicationContinuity.quot_zero {k r : ℕ} {μG μS νq : Measure (Formalism.QuantumDeterminants.Mt k r)} [SFinite μS]
    (hq : PI.BesselPeriodGGP.IsQuotMeas μG μS νq) (F : Formalism.QuantumDeterminants.Mt k r → ℂ) (hFm : Measurable F)
    (hFi : Integrable F μG) (hin : ∀ᵐ x ∂νq, ∫ s, F (mulMt s x) ∂μS = 0) : ∫ x, F x ∂μG = 0 := by sorry
