-- Prove2me | Theorems.Thm_Formalism_IrreducibleCountingLemmas_Z_card_value_ne_run_le
-- name    : Formalism.IrreducibleCountingLemmas.Z.card_value_ne_run_le
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T07:50:38.42355+00:00
-- url     : https://prove2.me/theorems/a5844b32-268e-4b6a-8da8-06f3c86a926d
-- title:
--   Z: card value ne run le
-- statement:
--   The Z construction uses the card value ne run le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PadicSubsetSums/StableGradedCounts/CardLtAddCardGtAddCardEq.lean#L145-L164
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PadicSubsetSums/StableGradedCounts/CardLtAddCardGtAddCardEq.lean#L145-L164

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

theorem Formalism.IrreducibleCountingLemmas.Z.card_value_ne_run_le (n p t : ℕ) (lam : Fin n → ℤ) (c : ℤ) (hpt : p + t ≤ n)
    (hrun : ∀ i : Fin n, lam i = c ↔ p ≤ (i : ℕ) ∧ (i : ℕ) < p + t) (c₀ : ℤ) (h : c₀ ≠ c) :
    (Finset.univ.filter fun j => lam j = c₀).card ≤ n - t := by sorry
