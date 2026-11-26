-- Prove2me | Theorems.Thm_BKAR_Forest_rootBoundarySupportOrderContribution_eq_treeFiber_of_edges_ne_empty
-- name    : BKAR.Forest.rootBoundarySupportOrderContribution_eq_treeFiber_of_edges_ne_empty
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T09:06:34.81737+00:00
-- url     : https://prove2.me/theorems/672d976b-9a93-5aeb-a859-62d11c06453c
-- title:
--   Forest: root Boundary Support Order Contribution eq tree Fiber of edges ne empty
-- statement:
--   The Forest construction uses the root Boundary Support Order Contribution eq tree Fiber of edges ne empty property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/OrderedAssembly/AllBranchesFibers.lean#L595-L607
-- source:
--   https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/OrderedAssembly/AllBranchesFibers.lean#L595-L607

import Definitions.Def_BKAR_OrderedAssembly_AllBranchesTelescoping
import Definitions.Def_BKAR_OrderedAssembly_AllBranchesFibers
set_option autoImplicit false
noncomputable section
open BKAR
open BKAR.Forest
variable {V : Type*} [Fintype V] [DecidableEq V]

theorem BKAR.Forest.rootBoundarySupportOrderContribution_eq_treeFiber_of_edges_ne_empty
    (choices : ActiveExtensionChoice V)
    (ρ : (Edge V → ℝ) → ℝ)
    (I : ForestIndex V) (order : List (Edge V))
    (hI : I.edges ≠ ∅) :
    rootBoundarySupportOrderContribution choices ρ I order =
      boundarySupportOrderTreeFiber choices (Forest.empty V) [] [] 1
        I order ρ := by sorry
