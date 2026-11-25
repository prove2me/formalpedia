-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_PBD_pick_one
-- name    : Formalism.FourierDecayAlt.P.PBD.pick_one
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T03:02:30.388797+00:00
-- url     : https://prove2.me/theorems/fda3dedd-1e20-5212-bab9-3fa7af33e72d
-- title:
--   PBD: pick one
-- statement:
--   The PBD construction uses the pick one property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/RoomOffGridSymmetric.lean#L37-L80
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/RoomOffGridSymmetric.lean#L37-L80

import Definitions.Def_Formalism_HermitianCurvature_RealInputsClosedAdmissibleSettings
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_RoomOffGridSymmetric
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.PBD
open Formalism.FourierDecayAlt NumberField

theorem Formalism.FourierDecayAlt.P.PBD.pick_one (lo hi : ℝ) (Q B : Finset ℝ) (h : 9 * ((Q.card : ℝ) + B.card) + 1 ≤ hi - lo) :
    ∃ y, lo ≤ y ∧ y + 1 ≤ hi ∧ y ∉ B ∧ y + 1 ∉ B ∧ ∀ q ∈ Q, 4 < |y - q| := by sorry
