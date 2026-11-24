-- Prove2me | Theorems.Thm_Formalism_IrreducibleCountingLemmas_GaloisIrreducibility_card_pow_class_le
-- name    : Formalism.IrreducibleCountingLemmas.GaloisIrreducibility.card_pow_class_le
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T07:43:37.71187+00:00
-- url     : https://prove2.me/theorems/650511f7-0f65-4ac9-ac0d-c52f716d2f05
-- title:
--   Galois Irreducibility: card pow class le
-- statement:
--   The Galois Irreducibility construction uses the card pow class le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PadicSubsetSums/StableGradedCounts/IRRExcludedCount.lean#L66-L110
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PadicSubsetSums/StableGradedCounts/IRRExcludedCount.lean#L66-L110

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

theorem Formalism.IrreducibleCountingLemmas.GaloisIrreducibility.card_pow_class_le (S : Finset ℕ) (Y : ℝ) (l j d : ℕ) (hl : l.Prime) (hd : 1 ≤ d)
    (hY : 1 ≤ Y) (hj : Y < (l : ℝ) ^ (4 * j))
    (hS : ∀ g ∈ S, Y ≤ (g : ℝ) ∧ (g : ℝ) ≤ 2 * Y ∧ l ^ j ∣ g ^ d - 1) :
    (S.card : ℝ) ≤ 2 * d * (Y ^ ((3 : ℝ) / 4) + 1) := by sorry
