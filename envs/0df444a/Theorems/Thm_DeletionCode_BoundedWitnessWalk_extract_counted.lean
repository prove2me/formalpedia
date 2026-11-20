-- Prove2me | Theorems.Thm_DeletionCode_BoundedWitnessWalk_extract_counted
-- name    : DeletionCode.BoundedWitnessWalk.extract_counted
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T06:32:55.315839+00:00
-- url     : https://prove2.me/theorems/befbb22f-0c96-4002-adb4-6130e3c8720e
-- title:
--   Bounded Witness Walk: extract counted
-- statement:
--   The extracted rule set satisfies the very predicate used by the concrete
--   counting theorem, while retaining independence and all witness bounds.
--
--   Source: https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/BoundedWitnessWalk.lean#L67-L80
-- source:
--   https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/BoundedWitnessWalk.lean#L67-L80

import Definitions.Def_DeletionCode_WitnessCases
import Definitions.Def_DeletionCode_FiniteWalkRules
import Definitions.Def_DeletionCode_GeneratingEnumeration
import Definitions.Def_DeletionCode_SpectrumPath
import Definitions.Def_DeletionCode_BoundedWitnessWalk
set_option autoImplicit true
open DeletionCode DeletionCode.BoundedWitnessWalk
open Windows HeaderRecovery SignedSupport SignedRuleCount RuleSetGraph ConnectedBlocks
open CatalogueAlgebra FiniteWalkRules WalkSelection BlockPartition WitnessCases

theorem DeletionCode.BoundedWitnessWalk.extract_counted {t k m n : ℕ} (ht : 2 ≤ t) (x : Letters)
    (p : Fin (m + 1) → Gram (windowLength k) → ℤ)
    (K : Set (Gram (windowLength k) → ℤ))
    (hbase : p 0 = wordSpectrum x n (windowLength k))
    (hp : ∀ j, WitnessAlgebra.BooleanVector (rationalPath p j))
    (hclosed : p 0 = p (Fin.last m)) (hodd : Odd m)
    (hcat : ∀ i, CatalogueRule t k (step p i))
    (hK : ∀ i, step p i ∈ K) :
    ∃ U : RuleSet k, Witness t k (wordSpectrum x n (windowLength k)) K U ∧
      ManuscriptCounting.GeneratingSet t x n k U.card (componentCount U) U := by sorry
