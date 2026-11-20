-- Prove2me | Theorems.Thm_DeletionCode_BoundedWitnessWalk_extract
-- name    : DeletionCode.BoundedWitnessWalk.extract
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T06:32:47.714337+00:00
-- url     : https://prove2.me/theorems/fe553547-eb1a-45b7-8207-31a3fc67114d
-- title:
--   Bounded Witness Walk: extract
-- statement:
--   An odd closed Boolean walk whose steps are surviving catalogue rules
--   contains an actual finite generating witness with all manuscript bounds.
--
--   Source: https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/BoundedWitnessWalk.lean#L20-L63
-- source:
--   https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/BoundedWitnessWalk.lean#L20-L63

import Definitions.Def_DeletionCode_WitnessCases
import Definitions.Def_DeletionCode_FiniteWalkRules
import Definitions.Def_DeletionCode_GeneratingEnumeration
import Definitions.Def_DeletionCode_SpectrumPath
import Definitions.Def_DeletionCode_BoundedWitnessWalk
set_option autoImplicit true
open DeletionCode DeletionCode.BoundedWitnessWalk
open Windows HeaderRecovery SignedSupport SignedRuleCount RuleSetGraph ConnectedBlocks
open CatalogueAlgebra FiniteWalkRules WalkSelection BlockPartition WitnessCases

theorem DeletionCode.BoundedWitnessWalk.extract {t k m : ℕ} (ht : 2 ≤ t)
    (p : Fin (m + 1) → Gram (windowLength k) → ℤ)
    (K : Set (Gram (windowLength k) → ℤ))
    (hp : ∀ j, WitnessAlgebra.BooleanVector (rationalPath p j))
    (hclosed : p 0 = p (Fin.last m)) (hodd : Odd m)
    (hcat : ∀ i, CatalogueRule t k (step p i))
    (hK : ∀ i, step p i ∈ K) :
    ∃ U : RuleSet k, Witness t k (p 0) K U := by sorry
