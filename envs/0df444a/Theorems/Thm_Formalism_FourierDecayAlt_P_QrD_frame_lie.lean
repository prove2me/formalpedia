-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_QrD_frame_lie
-- name    : Formalism.FourierDecayAlt.P.QrD.frame_lie
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T01:36:28.349+00:00
-- url     : https://prove2.me/theorems/f4735e0f-bdf9-4a27-a58b-6e82390a3828
-- title:
--   Qr D: frame lie
-- statement:
--   The Qr D construction uses the frame lie property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/RightTypeAction.lean#L38-L52
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/RightTypeAction.lean#L38-L52

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
variable {k r : ℕ}

theorem Formalism.FourierDecayAlt.P.QrD.frame_lie {m : ℕ} {z : Fin (2 * r + k + 1) → ℂ} {Bs : Fin m → Fin (2 * r + k + 1) → ℂ}
    (hB : IsFrameOf k r [z] Bs) (a b : Fin m) :
    InLieW k r z (hpart1 (Hpk k r) (unitB (Hpk k r) Bs a b)) ∧
      InLieW k r z (hpart2 (Hpk k r) (unitB (Hpk k r) Bs a b)) := by sorry
