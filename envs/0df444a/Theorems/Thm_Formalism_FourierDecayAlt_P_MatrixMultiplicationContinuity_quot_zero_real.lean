-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_MatrixMultiplicationContinuity_quot_zero_real
-- name    : Formalism.FourierDecayAlt.P.MatrixMultiplicationContinuity.quot_zero_real
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-24T16:17:23.652224+00:00
-- url     : https://prove2.me/theorems/d983b32c-af77-4a2c-a057-b5b585e8b921
-- title:
--   Matrix Multiplication Continuity: quot zero real
-- statement:
--   The Matrix Multiplication Continuity construction uses the quot zero real property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/ContinuousMulMt.lean#L34-L68
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/ContinuousMulMt.lean#L34-L68

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

theorem Formalism.FourierDecayAlt.P.MatrixMultiplicationContinuity.quot_zero_real {k r : ℕ} {μG μS νq : Measure (Formalism.QuantumDeterminants.Mt k r)} [SFinite μS]
    (hq : PI.BesselPeriodGGP.IsQuotMeas μG μS νq) (f : Formalism.QuantumDeterminants.Mt k r → ℝ) (hfm : Measurable f)
    (hfi : Integrable f μG) (hin : ∀ᵐ x ∂νq, ∫ s, f (mulMt s x) ∂μS = 0) : ∫ x, f x ∂μG = 0 := by sorry
