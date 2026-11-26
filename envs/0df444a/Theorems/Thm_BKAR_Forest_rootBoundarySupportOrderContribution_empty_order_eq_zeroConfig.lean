-- Prove2me | Theorems.Thm_BKAR_Forest_rootBoundarySupportOrderContribution_empty_order_eq_zeroConfig
-- name    : BKAR.Forest.rootBoundarySupportOrderContribution_empty_order_eq_zeroConfig
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T09:03:55.120249+00:00
-- url     : https://prove2.me/theorems/394b8867-531d-4efc-b30e-6c28ea00e162
-- title:
--   Forest: root Boundary Support Order Contribution empty order eq zero Config
-- statement:
--   The Forest construction uses the root Boundary Support Order Contribution empty order eq zero Config property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/OrderedAssembly/AllBranchesFibers.lean#L554-L563
-- source:
--   https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/OrderedAssembly/AllBranchesFibers.lean#L554-L563

import Definitions.Def_BKAR_OrderedAssembly_AllBranchesTelescoping
import Definitions.Def_BKAR_OrderedAssembly_AllBranchesFibers
set_option autoImplicit false
noncomputable section
open BKAR
open BKAR.Forest
variable {V : Type*} [Fintype V] [DecidableEq V]

theorem BKAR.Forest.rootBoundarySupportOrderContribution_empty_order_eq_zeroConfig
    (choices : ActiveExtensionChoice V)
    (ρ : (Edge V → ℝ) → ℝ)
    (I : ForestIndex V)
    (hI : I.edges = ∅) :
    rootBoundarySupportOrderContribution choices ρ I [] = ρ zeroConfig := by sorry
