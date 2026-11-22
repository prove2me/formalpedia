-- Prove2me | Theorems.Thm_Formalism_REAL_sum_sum_sub_sum_sum_swap
-- name    : Formalism.REAL.sum_sum_sub_sum_sum_swap
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-22T23:10:04.803321+00:00
-- url     : https://prove2.me/theorems/8be09442-dd3c-49a1-b81b-0782ddb1a639
-- title:
--   REAL: sum sum sub sum sum swap
-- statement:
--   The REAL construction uses the sum sum sub sum sum swap property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/RealPlaceAnalysis/RealPlaceTaylor/SatisfiesGlRelationsBilinearLeft.lean#L123-L128
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/RealPlaceAnalysis/RealPlaceTaylor/SatisfiesGlRelationsBilinearLeft.lean#L123-L128

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

theorem Formalism.REAL.sum_sum_sub_sum_sum_swap {A α β : Type*} [AddCommGroup A] [Fintype α] [Fintype β] (f : α → β → A)
    (g : β → α → A) :
    ∑ x, ∑ y, f x y - ∑ y, ∑ x, g y x = ∑ x, ∑ y, (f x y - g y x) := by sorry
