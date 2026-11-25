-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_QrD_exp_uw
-- name    : Formalism.FourierDecayAlt.P.QrD.exp_uw
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T01:34:31.11711+00:00
-- url     : https://prove2.me/theorems/e29e720d-a0de-4649-b411-b446d648b4b0
-- title:
--   Qr D: exp uw
-- statement:
--   The Qr D construction uses the exp uw property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/RightTypeAction.lean#L23-L26
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/RightTypeAction.lean#L23-L26

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

theorem Formalism.FourierDecayAlt.P.QrD.exp_uw {z : Fin (2 * r + k + 1) → ℂ} {X : Mx k r} (hX : InLieW k r z X) (t : ℝ) :
    NormedSpace.exp ((t : ℂ) • X) ∈ UWset k r z := by sorry
