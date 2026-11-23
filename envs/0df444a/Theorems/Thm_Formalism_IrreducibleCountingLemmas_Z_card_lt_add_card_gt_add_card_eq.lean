-- Prove2me | Theorems.Thm_Formalism_IrreducibleCountingLemmas_Z_card_lt_add_card_gt_add_card_eq
-- name    : Formalism.IrreducibleCountingLemmas.Z.card_lt_add_card_gt_add_card_eq
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T04:09:36.245848+00:00
-- url     : https://prove2.me/theorems/7504595b-f2b2-4f96-b6f0-c3604380c1ed
-- title:
--   Z: card lt add card gt add card eq
-- statement:
--   The Z construction uses the card lt add card gt add card eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PadicSubsetSums/StableGradedCounts/CardLtAddCardGtAddCardEq.lean#L166-L174
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PadicSubsetSums/StableGradedCounts/CardLtAddCardGtAddCardEq.lean#L166-L174

import Definitions.Def_Formalism_PadicSubsetSums_CentralIdempotents_FactorOverLocalSubalgebraMonic
import Definitions.Def_Formalism_PadicSubsetSums_StableGradedCounts_ZReuse
import Definitions.Def_Formalism_PadicSubsetSums_StableGradedCounts_ZCircleCharExtends
import Definitions.Def_Formalism_PadicSubsetSums_StableGradedCounts_FactorOverLocalSubalgebra
import Definitions.Def_Formalism_PadicSubsetSums_StableGradedCounts_CharpolyFactorAnnihilator
import Definitions.Def_Formalism_PadicSubsetSums_StableGradedCounts_ZGoodCuspidal
import Definitions.Def_Formalism_PadicSubsetSums_StableGradedCounts_ZBrauerNesbitt
import Definitions.Def_Formalism_PadicSubsetSums_StableGradedCounts_CardLtAddCardGtAddCardEq
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Polynomial Filter Topology
open Formalism Formalism.IrreducibleCountingLemmas Formalism.IrreducibleCountingLemmas.Z

theorem Formalism.IrreducibleCountingLemmas.Z.card_lt_add_card_gt_add_card_eq (n : ℕ) (lam : Fin n → ℤ) (c₀ : ℤ) :
    (Finset.univ.filter fun j => c₀ < lam j).card + (Finset.univ.filter fun j => lam j < c₀).card +
      (Finset.univ.filter fun j => lam j = c₀).card = n := by sorry
