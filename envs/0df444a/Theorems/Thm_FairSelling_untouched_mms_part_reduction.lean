-- Prove2me | Theorems.Thm_FairSelling_untouched_mms_part_reduction
-- name    : FairSelling.untouched_mms_part_reduction
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T01:39:11.943354+00:00
-- url     : https://prove2.me/theorems/f4d197d0-524c-40e1-968c-972a4e8e479c
-- title:
--   Fair Selling: untouched mms part reduction
-- statement:
--   The Fair Selling construction uses the untouched mms part reduction property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/yotam-gafni/FairAllocationWithOptionalSelling/blob/daed8afbbc6b4da634e8cbffa11e861f99533f56/RequestProject/ThreeAgents.lean#L426-L457
-- source:
--   https://github.com/yotam-gafni/FairAllocationWithOptionalSelling/blob/daed8afbbc6b4da634e8cbffa11e861f99533f56/RequestProject/ThreeAgents.lean#L426-L457

import Mathlib
import Definitions.Def_RequestProject_SmallN
import Definitions.Def_RequestProject_TwoAgents
import Definitions.Def_RequestProject_MMSPartition
import Definitions.Def_RequestProject_ThreeAgents
set_option autoImplicit true
open scoped BigOperators
open FairSelling
variable {G : Type*} [Fintype G] [DecidableEq G]

theorem FairSelling.untouched_mms_part_reduction (w p : G → ℝ) (hw : ∀ g, 0 ≤ w g) (hp : ∀ g, 0 ≤ p g)
    (A : Fin 3 → Finset G) (s : Finset G) (q : Fin 3 → ℝ)
    (hcfg : ConfigN 3 w p (MMS 3 w p) A s q)
    (lost j k : Fin 3) (hlj : lost ≠ j) (hlk : lost ≠ k) (hjk : j ≠ k)
    (g : G) (hg : g ∈ A lost) :
    MMS 3 w p ≤ MMS 2 (restrictVal (Finset.univ \ {g}) w)
      (restrictVal (Finset.univ \ {g}) p) := by sorry
