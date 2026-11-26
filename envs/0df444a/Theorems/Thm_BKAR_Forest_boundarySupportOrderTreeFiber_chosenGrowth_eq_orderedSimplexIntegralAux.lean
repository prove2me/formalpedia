-- Prove2me | Theorems.Thm_BKAR_Forest_boundarySupportOrderTreeFiber_chosenGrowth_eq_orderedSimplexIntegralAux
-- name    : BKAR.Forest.boundarySupportOrderTreeFiber_chosenGrowth_eq_orderedSimplexIntegralAux
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T09:19:21.745798+00:00
-- url     : https://prove2.me/theorems/46ab891a-6d22-4d49-a374-958e9c60e1a9
-- title:
--   Forest: boundary Support Order Tree Fiber chosen Growth eq ordered Simplex Integral Aux
-- statement:
--   Along a chosen growth path, the fixed support/order tree fiber is exactly the
--   corresponding ordered simplex integral.  This is the arbitrary finite-order
--   version of the explicit one- and two-edge bridge lemmas below.
--
--   Source: https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/OrderedAssembly/AllBranchesFiberBridge/Core.lean#L489-L560
-- source:
--   https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/OrderedAssembly/AllBranchesFiberBridge/Core.lean#L489-L560

import Definitions.Def_BKAR_OrderedAssembly_AllBranchesFiberBridge_FollowOrder
import Definitions.Def_BKAR_OrderedAssembly_AllBranchesFiberBridge_Core
import Theorems.Thm_BKAR_EdgePath_IsSimplePath_reverse

set_option autoImplicit false
noncomputable section
open BKAR
open BKAR.Forest
variable {V : Type*} [Fintype V] [DecidableEq V]

theorem BKAR.Forest.boundarySupportOrderTreeFiber_chosenGrowth_eq_orderedSimplexIntegralAux
    (choices : ActiveExtensionChoice V)
    {F G : Forest V} {order : List (Edge V)}
    (path : ChosenGrowth choices F order G) :
    ∀ (pref : List (Edge V)) (prefixTs : List ℝ) (top : ℝ)
      (ρ : (Edge V → ℝ) → ℝ),
      order ≠ [] →
      boundarySupportOrderTreeFiber choices F pref prefixTs top
          G.support (pref ++ order) ρ =
        orderedSimplexIntegralAux top order
          (fun ts => mixedPartialList (pref ++ order).reverse ρ
            (G.standardInterp
              (G.paramsOfOrder (pref ++ order) (prefixTs ++ ts))))
  := by sorry
