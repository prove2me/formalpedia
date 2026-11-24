-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_Qx6_opL_lin
-- name    : Formalism.FourierDecayAlt.P.Qx6.opL_lin
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-24T16:34:45.702363+00:00
-- url     : https://prove2.me/theorems/11f964fa-440d-486d-803e-ce4740a46071
-- title:
--   Qx6: op L lin
-- statement:
--   The Qx6 construction uses the op L lin property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/ChainRecursionFromSingleDescent.lean#L1084-L1113
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/ChainRecursionFromSingleDescent.lean#L1084-L1113

import Definitions.Def_Formalism_HermitianCurvature_StatementQ
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_GeneratorCommutatorQuantumDet
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_SumDualVectorEqZeta
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_WeylCellConjTransposeMulApply
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ChainRecursionFromSingleDescent
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
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.Qx6
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.Q
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {k r : ℕ}
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

theorem Formalism.FourierDecayAlt.P.Qx6.opL_lin (a : Fin r) (j : Fin 6) {f₁ f₂ : (Fin r → ℂ) → E} {c : Fin r → ℂ} (s : ℂ)
    (h1 : DifferentiableAt ℝ f₁ c) (h2 : DifferentiableAt ℝ f₂ c) :
    opL a j (fun x => f₁ x + s • f₂ x) c = opL a j f₁ c + s • opL a j f₂ c := by sorry
