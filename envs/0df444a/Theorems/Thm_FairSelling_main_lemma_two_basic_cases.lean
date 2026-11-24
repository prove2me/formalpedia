-- Prove2me | Theorems.Thm_FairSelling_main_lemma_two_basic_cases
-- name    : FairSelling.main_lemma_two_basic_cases
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T02:36:46.173832+00:00
-- url     : https://prove2.me/theorems/4e5cd33e-1af4-45cd-956f-9f2a33d4923f
-- title:
--   Fair Selling: main lemma two basic cases
-- statement:
--   The Fair Selling construction uses the main lemma two basic cases property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/yotam-gafni/FairAllocationWithOptionalSelling/blob/daed8afbbc6b4da634e8cbffa11e861f99533f56/RequestProject/ThreeAgents.lean#L466-L479
-- source:
--   https://github.com/yotam-gafni/FairAllocationWithOptionalSelling/blob/daed8afbbc6b4da634e8cbffa11e861f99533f56/RequestProject/ThreeAgents.lean#L466-L479

import Mathlib
import Definitions.Def_RequestProject_SmallN
import Definitions.Def_RequestProject_TwoAgents
import Definitions.Def_RequestProject_MMSPartition
import Definitions.Def_RequestProject_ThreeAgents
set_option autoImplicit true
open scoped BigOperators
open FairSelling
variable {G : Type*} [Fintype G] [DecidableEq G]

theorem FairSelling.main_lemma_two_basic_cases (w p : G → ℝ) (hw : ∀ g, 0 ≤ w g) (hp : ∀ g, 0 ≤ p g)
    (hnobig : ∀ g, vbar w p g < (3/4) * MMS 3 w p) (B : Finset G)
    (hcase : vbarSum w p B ≤ (3/4) * MMS 3 w p ∨
      ∃ (A : Fin 3 → Finset G) (s : Finset G) (q : Fin 3 → ℝ)
        (lost j k : Fin 3) (g : G),
        B = {g} ∧ ConfigN 3 w p (MMS 3 w p) A s q ∧
        lost ≠ j ∧ lost ≠ k ∧ j ≠ k ∧ g ∈ A lost) :
    (3/4) * MMS 3 w p ≤
      MMS 2 (restrictVal (Finset.univ \ B) w) (restrictVal (Finset.univ \ B) p) := by sorry
