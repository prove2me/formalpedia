-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_MatrixMultiplicationContinuity_psi_cont
-- name    : Formalism.FourierDecayAlt.P.MatrixMultiplicationContinuity.psi_cont
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T03:17:07.577734+00:00
-- url     : https://prove2.me/theorems/78847117-2470-56ec-97b5-d90bf9e995b8
-- title:
--   Matrix Multiplication Continuity: psi cont
-- statement:
--   The Matrix Multiplication Continuity construction uses the psi cont property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/ReproducingFormulaReduction.lean#L23-L33
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/ReproducingFormulaReduction.lean#L23-L33

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

theorem Formalism.FourierDecayAlt.P.MatrixMultiplicationContinuity.psi_cont (z : Fin (2 * r + k + 1) → ℂ) (c : ℂ) :
    Continuous (fun g : Mx k r => Formalism.QuantumDeterminants.psi k r z c g) := by sorry
