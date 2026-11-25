-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_QrD_ecRep_eq
-- name    : Formalism.FourierDecayAlt.P.QrD.ecRep_eq
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T01:45:31.987038+00:00
-- url     : https://prove2.me/theorems/7b283a5d-27d8-5f3e-ae38-2c2e02f9d52a
-- title:
--   Qr D: ec Rep eq
-- statement:
--   The Qr D construction uses the ec Rep eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/RightTypeAction.lean#L90-L95
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/RightTypeAction.lean#L90-L95

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

theorem Formalism.FourierDecayAlt.P.QrD.ecRep_eq (hπ : IsCRepOn (UWset k r z) π) (hc : ContinuousOn π (UWset k r z)) {Z : Mx k r}
    (h1 : InLieW k r z (hpart1 (Hpk k r) Z)) (h2 : InLieW k r z (hpart2 (Hpk k r) Z)) (v : W) :
    EcRep (Hpk k r) π Z v = ecOp π Z v := by sorry
