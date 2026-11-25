-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_QrD_dOp_hasDeriv
-- name    : Formalism.FourierDecayAlt.P.QrD.dOp_hasDeriv
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T01:34:37.642707+00:00
-- url     : https://prove2.me/theorems/0d1469cf-4b5a-4a8c-84ab-96a93d4df492
-- title:
--   Qr D: d Op has Deriv
-- statement:
--   The Qr D construction uses the d Op has Deriv property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/RightTypeAction.lean#L68-L79
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/RightTypeAction.lean#L68-L79

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_OneParameterDifferentiable
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_RestrictionIrrelevantDoubleLevelOperator
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_RightTypeAction
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Finset Filter Topology
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.Q
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
open Formalism.FourierDecayAlt.P.QrD
variable {k r : ℕ} {W : Type} [NormedAddCommGroup W] [NormedSpace ℂ W]
variable [FiniteDimensional ℂ W] {z : Fin (2 * r + k + 1) → ℂ} {π : Mx k r → (W →L[ℂ] W)}

theorem Formalism.FourierDecayAlt.P.QrD.dOp_hasDeriv (hπ : IsCRepOn (UWset k r z) π) (hc : ContinuousOn π (UWset k r z)) {X : Mx k r}
    (hX : InLieW k r z X) : HasDerivAt (fun t : ℝ => π (NormedSpace.exp ((t : ℂ) • X))) (dOp π X) 0 := by sorry
