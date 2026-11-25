-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_left_type_action
-- name    : Formalism.FourierDecayAlt.P.left_type_action
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T02:04:53.943038+00:00
-- url     : https://prove2.me/theorems/5ae6e2e8-236b-517b-8981-412e9070b074
-- title:
--   P: left type action
-- statement:
--   The P construction uses the left type action property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/LeftTypeAction.lean#L114-L132
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/LeftTypeAction.lean#L114-L132

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_RightTypeAction
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_LeftTypeAction
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

theorem Formalism.FourierDecayAlt.P.left_type_action : Formalism.FourierDecayAlt.Q.LeftTypeAction := by sorry
