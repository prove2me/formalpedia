-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_PBD_pick_many
-- name    : Formalism.FourierDecayAlt.P.PBD.pick_many
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T03:00:18.542405+00:00
-- url     : https://prove2.me/theorems/997698f1-c0bc-4d15-b29e-80d64a030f9f
-- title:
--   PBD: pick many
-- statement:
--   The PBD construction uses the pick many property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/RoomOffGridSymmetric.lean#L82-L102
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/RoomOffGridSymmetric.lean#L82-L102

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

theorem Formalism.FourierDecayAlt.P.PBD.pick_many (lo hi : ℝ) (B : Finset ℝ) : ∀ (m : ℕ) (Q : Finset ℝ),
    9 * ((Q.card : ℝ) + m + B.card) + 1 ≤ hi - lo →
    ∃ ys : List ℝ, ys.length = m ∧
      (∀ y ∈ ys, lo ≤ y ∧ y + 1 ≤ hi ∧ y ∉ B ∧ y + 1 ∉ B ∧ ∀ q ∈ Q, 4 < |y - q|) ∧
      ys.Pairwise (fun y y' => 4 < |y - y'|)
  := by sorry
