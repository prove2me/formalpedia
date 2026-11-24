-- Prove2me | Theorems.Thm_Formalism_MainNotions_Gaps_T0_ql_scaled_le
-- name    : Formalism.MainNotions.Gaps.T0.ql_scaled_le
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-24T09:56:24.56416+00:00
-- url     : https://prove2.me/theorems/5aa6a118-30e3-47e0-8d27-9f78653a70fd
-- title:
--   T0: ql scaled le
-- statement:
--   The T0 construction uses the ql scaled le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/GenusPolyhedralBounds/RelativeIndexClassSets/LengthLeOfSemilinear.lean#L30-L43
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/GenusPolyhedralBounds/RelativeIndexClassSets/LengthLeOfSemilinear.lean#L30-L43

import Definitions.Def_Formalism_FilteredPoleLength_LocalDescentLevels_LocalStepClosed
import Definitions.Def_Formalism_FilteredPoleLength_LocalDescentLevels_LocalStepDescent
import Definitions.Def_Formalism_SharpRestriction_GenusPolyhedralBounds_RelativeIndexClassSets_LengthLeOfSemilinear
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism Formalism.MainNotions Formalism.MainNotions.Gaps Formalism.MainNotions.Gaps.T0
open Module Formalism.LatticeBaseChangeAlt Formalism.LatticeBaseChangeAlt.BQuot
variable {O V W : Type*} [CommRing O] [AddCommGroup V] [Module O V] [AddCommGroup W] [Module O W]

theorem Formalism.MainNotions.Gaps.T0.ql_scaled_le (r : O) (M Mgg NK : Submodule O V) {n : ℕ} (th : Fin n → V) (h1 : Mgg ≤ M)
    (h2 : Mgg ≤ NK) :
    ql (M.map (r • (LinearMap.id : V →ₗ[O] V)))
        ((M.map (r • (LinearMap.id : V →ₗ[O] V)) ⊓ NK) ⊔
          Submodule.span O (Set.range fun j => r • th j)) ≤
      ql M (Mgg ⊔ Submodule.span O (Set.range th)) := by sorry
