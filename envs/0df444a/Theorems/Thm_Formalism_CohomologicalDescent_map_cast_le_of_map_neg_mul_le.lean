-- Prove2me | Theorems.Thm_Formalism_CohomologicalDescent_map_cast_le_of_map_neg_mul_le
-- name    : Formalism.CohomologicalDescent.map_cast_le_of_map_neg_mul_le
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-24T22:45:16.268805+00:00
-- url     : https://prove2.me/theorems/9e38e727-8ef2-49fd-a97d-59fe9e4bd1a9
-- title:
--   Cohomological Descent: map cast le of map neg mul le
-- statement:
--   The Cohomological Descent construction uses the map cast le of map neg mul le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PieriBlockIdeals/PieriColumnMinors/RegularCuspidalTrace.lean#L26-L37
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PieriBlockIdeals/PieriColumnMinors/RegularCuspidalTrace.lean#L26-L37

import Mathlib
import Definitions.Def_Formalism_PieriBlockIdeals_LemmaWAssembled
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_MinorValuationBoundHolds
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_WeightExchangeChainHolds
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_RegularCuspidalTrace
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Finset
open Formalism Formalism.CohomologicalDescent

theorem Formalism.CohomologicalDescent.map_cast_le_of_map_neg_mul_le (l : ℕ) (hl : l.Prime) (F : Type) [Field F] [CharP F l] (a : F) (ha : a ≠ 0)
    {α β : Type} (A : Multiset α) (B : Multiset β) (f : α → ℤ) (g : β → ℤ)
    (h : Multiset.map (fun x => -a * ((f x : ℤ) : F)) A ≤
      Multiset.map (fun y => -a * ((g y : ℤ) : F)) B) :
    Multiset.map (fun x => ((f x : ℤ) : ZMod l)) A ≤ Multiset.map (fun y => ((g y : ℤ) : ZMod l)) B := by sorry
