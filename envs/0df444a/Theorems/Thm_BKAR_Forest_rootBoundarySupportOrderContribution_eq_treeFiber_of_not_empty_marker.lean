-- Prove2me | Theorems.Thm_BKAR_Forest_rootBoundarySupportOrderContribution_eq_treeFiber_of_not_empty_marker
-- name    : BKAR.Forest.rootBoundarySupportOrderContribution_eq_treeFiber_of_not_empty_marker
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T09:04:54.696341+00:00
-- url     : https://prove2.me/theorems/c6d27ca7-ea65-553c-8de1-1e308b3dc77a
-- title:
--   Forest: root Boundary Support Order Contribution eq tree Fiber of not empty marker
-- statement:
--   The Forest construction uses the root Boundary Support Order Contribution eq tree Fiber of not empty marker property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/OrderedAssembly/AllBranchesFibers.lean#L583-L593
-- source:
--   https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/OrderedAssembly/AllBranchesFibers.lean#L583-L593

import Definitions.Def_BKAR_OrderedAssembly_AllBranchesTelescoping
import Definitions.Def_BKAR_OrderedAssembly_AllBranchesFibers
set_option autoImplicit false
noncomputable section
open BKAR
open BKAR.Forest
variable {V : Type*} [Fintype V] [DecidableEq V]

theorem BKAR.Forest.rootBoundarySupportOrderContribution_eq_treeFiber_of_not_empty_marker
    (choices : ActiveExtensionChoice V)
    (ρ : (Edge V → ℝ) → ℝ)
    (I : ForestIndex V) (order : List (Edge V))
    (hmarker : ¬ (I.edges = ∅ ∧ order = [])) :
    rootBoundarySupportOrderContribution choices ρ I order =
      boundarySupportOrderTreeFiber choices (Forest.empty V) [] [] 1
        I order ρ := by sorry
