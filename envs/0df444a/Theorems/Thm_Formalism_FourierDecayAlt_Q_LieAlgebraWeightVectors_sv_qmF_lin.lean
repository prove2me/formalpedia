-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_Q_LieAlgebraWeightVectors_sv_qmF_lin
-- name    : Formalism.FourierDecayAlt.Q.LieAlgebraWeightVectors.sv_qmF_lin
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-24T16:47:35.545479+00:00
-- url     : https://prove2.me/theorems/5ae1d3b2-8e14-407a-b6fd-8e0a55b26229
-- title:
--   Lie Algebra Weight Vectors: sv qm F lin
-- statement:
--   The Lie Algebra Weight Vectors construction uses the sv qm F lin property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/QuadraticFormTwoTwo/SmoothVec.lean#L313-L342
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/QuadraticFormTwoTwo/SmoothVec.lean#L313-L342

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_QuadraticFormTwoTwo_InLieW
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_QuadraticFormTwoTwo_SmoothVec
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Finset Filter Topology
open scoped ContDiff
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.Q.LieAlgebraWeightVectors
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.P
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

theorem Formalism.FourierDecayAlt.Q.LieAlgebraWeightVectors.sv_qmF_lin {X : Type*} [AddCommGroup X] [Module ℂ X] {n t : ℕ} (Eop : Fin n → Fin n → X → X)
    (hE : ∀ a b, IsLinearMap ℂ (Eop a b)) (a b : Fin t → Fin n) (u : ℂ) : IsLinearMap ℂ (qmF Eop a b u) := by sorry
