-- Prove2me | Theorems.Thm_BKAR_Forest_rootBoundarySupportOrderContribution_eq_zeroConfig_of_edges_eq_empty
-- name    : BKAR.Forest.rootBoundarySupportOrderContribution_eq_zeroConfig_of_edges_eq_empty
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T09:50:00.573687+00:00
-- url     : https://prove2.me/theorems/cbb96ff4-575b-5abd-be46-665c6a6b611f
-- title:
--   Forest: root Boundary Support Order Contribution eq zero Config of edges eq empty
-- statement:
--   The Forest construction uses the root Boundary Support Order Contribution eq zero Config of edges eq empty property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/OrderedAssembly/AllBranchesFibers.lean#L565-L581
-- source:
--   https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/OrderedAssembly/AllBranchesFibers.lean#L565-L581

import Definitions.Def_BKAR_OrderedAssembly_AllBranchesTelescoping
import Definitions.Def_BKAR_OrderedAssembly_AllBranchesFibers
set_option autoImplicit false
noncomputable section
open BKAR
open BKAR.Forest
variable {V : Type*} [Fintype V] [DecidableEq V]

theorem BKAR.Forest.rootBoundarySupportOrderContribution_eq_zeroConfig_of_edges_eq_empty
    (choices : ActiveExtensionChoice V)
    (ρ : (Edge V → ℝ) → ℝ)
    (I : ForestIndex V) (order : List (Edge V))
    (hI : I.edges = ∅)
    (horder : order ∈ edgeSetOrders I.edges) :
    rootBoundarySupportOrderContribution choices ρ I order =
      ρ zeroConfig := by sorry
