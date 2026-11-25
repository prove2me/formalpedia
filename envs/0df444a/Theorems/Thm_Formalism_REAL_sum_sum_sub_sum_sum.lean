-- Prove2me | Theorems.Thm_Formalism_REAL_sum_sum_sub_sum_sum
-- name    : Formalism.REAL.sum_sum_sub_sum_sum
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T11:51:52.087242+00:00
-- url     : https://prove2.me/theorems/993be0e9-123e-5a2c-bf15-d9b6bb7dd766
-- title:
--   REAL: sum sum sub sum sum
-- statement:
--   The REAL construction uses the sum sum sub sum sum property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/RealPlaceAnalysis/RealPlaceTaylor/SatisfiesGlRelationsBilinearLeft.lean#L119-L121
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/RealPlaceAnalysis/RealPlaceTaylor/SatisfiesGlRelationsBilinearLeft.lean#L119-L121

import Definitions.Def_Formalism_RealPlaceAnalysis_FockPairGl
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_SatisfiesGlRelationsBilinearLeft
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MvPolynomial
noncomputable section
open Formalism Formalism.REAL

theorem Formalism.REAL.sum_sum_sub_sum_sum {A α β : Type*} [AddCommGroup A] [Fintype α] [Fintype β] (f g : α → β → A) :
    ∑ x, ∑ y, f x y - ∑ x, ∑ y, g x y = ∑ x, ∑ y, (f x y - g x y) := by sorry
