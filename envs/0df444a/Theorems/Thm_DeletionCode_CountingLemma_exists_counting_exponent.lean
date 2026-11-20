-- Prove2me | Theorems.Thm_DeletionCode_CountingLemma_exists_counting_exponent
-- name    : DeletionCode.CountingLemma.exists_counting_exponent
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T06:18:34.658163+00:00
-- url     : https://prove2.me/theorems/e946d6f9-e711-4403-9e73-0a4e5ebb3213
-- title:
--   Counting Lemma: exists counting exponent
-- statement:
--   One integer depending only on t works for every base word, size and component count.
--
--   Source: https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/CountingLemma.lean#L71-L77
-- source:
--   https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/CountingLemma.lean#L71-L77

import Definitions.Def_DeletionCode_SignedRuleCount
import Definitions.Def_DeletionCode_RuleSetGraph
import Definitions.Def_DeletionCode_CountExponent
import Definitions.Def_DeletionCode_CountingLemma
set_option autoImplicit true
open DeletionCode DeletionCode.CountingLemma
open Windows HeaderRecovery GeneratingModel SignedSupport RuleReconstruction
open RuleSetGraph SignedRuleCount DescriptionCount CountExponent

theorem DeletionCode.CountingLemma.exists_counting_exponent (t : ℕ) (ht : 1 ≤ t) :
    ∃ a : ℕ, 1 ≤ a ∧ ∀ (x : Letters) (n k R c : ℕ),
      1 ≤ R → KUnique x n k → ∀ group : Fin (2 * t * R) → Fin R,
        Nat.card {Q : RuleSet k // GeneratingSet x n k (2 * t * R) R c group Q} ≤
          n ^ c * (windowLength k * R) ^ (a * R) := by sorry
