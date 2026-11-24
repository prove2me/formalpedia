-- Prove2me | Theorems.Thm_Formalism_IrreducibleCountingLemmas_GaloisIrreducibility_card_class_le
-- name    : Formalism.IrreducibleCountingLemmas.GaloisIrreducibility.card_class_le
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T07:43:19.471003+00:00
-- url     : https://prove2.me/theorems/418fd071-a40f-419f-82a2-e1431e037674
-- title:
--   Galois Irreducibility: card class le
-- statement:
--   The Galois Irreducibility construction uses the card class le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PadicSubsetSums/StableGradedCounts/IRRExcludedCount.lean#L6-L45
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PadicSubsetSums/StableGradedCounts/IRRExcludedCount.lean#L6-L45

import Definitions.Def_Formalism_PadicSubsetSums_StableGradedCounts_IRRBBCard
import Definitions.Def_Formalism_PadicSubsetSums_StableGradedCounts_IRRBBDivides
import Definitions.Def_Formalism_PadicSubsetSums_StableGradedCounts_IRRExcludedCount
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.IrreducibleCountingLemmas Formalism.IrreducibleCountingLemmas.GaloisIrreducibility

theorem Formalism.IrreducibleCountingLemmas.GaloisIrreducibility.card_class_le (S : Finset ℕ) (Y : ℝ) (M r : ℕ) (hM : 0 < M) (hY : 0 ≤ Y)
    (hS : ∀ g ∈ S, Y ≤ (g : ℝ) ∧ (g : ℝ) ≤ 2 * Y ∧ g % M = r) :
    (S.card : ℝ) ≤ Y / M + 1 := by sorry
