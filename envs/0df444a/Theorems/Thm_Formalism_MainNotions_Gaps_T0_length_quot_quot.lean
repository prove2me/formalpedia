-- Prove2me | Theorems.Thm_Formalism_MainNotions_Gaps_T0_length_quot_quot
-- name    : Formalism.MainNotions.Gaps.T0.length_quot_quot
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T11:51:16.128897+00:00
-- url     : https://prove2.me/theorems/28849ef6-0ee5-50bb-9fad-6b69d1f0de87
-- title:
--   T0: length quot quot
-- statement:
--   The T0 construction uses the length quot quot property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/GenusPolyhedralBounds/RelativeIndexClassSets/LengthLeOfSemilinear.lean#L47-L65
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/GenusPolyhedralBounds/RelativeIndexClassSets/LengthLeOfSemilinear.lean#L47-L65

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

theorem Formalism.MainNotions.Gaps.T0.length_quot_quot {O V : Type*} [CommRing O] [AddCommGroup V] [Module O V]
    (M Mgg : Submodule O V) {n : ℕ} (th : Fin n → V) (h1 : Mgg ≤ M) (h2 : ∀ j, th j ∈ M) :
    Module.length O ((↥M ⧸ Mgg.comap M.subtype) ⧸ Submodule.span O (Set.range fun j =>
        (Submodule.Quotient.mk ⟨th j, h2 j⟩ : ↥M ⧸ Mgg.comap M.subtype))) =
      Module.length O (↥M ⧸ (Mgg ⊔ Submodule.span O (Set.range th)).comap M.subtype) := by sorry
