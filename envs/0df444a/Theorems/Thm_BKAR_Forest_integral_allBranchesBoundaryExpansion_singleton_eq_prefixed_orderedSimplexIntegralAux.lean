-- Prove2me | Theorems.Thm_BKAR_Forest_integral_allBranchesBoundaryExpansion_singleton_eq_prefixed_orderedSimplexIntegralAux
-- name    : BKAR.Forest.integral_allBranchesBoundaryExpansion_singleton_eq_prefixed_orderedSimplexIntegralAux
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T09:44:47.134203+00:00
-- url     : https://prove2.me/theorems/65b37839-8287-5448-8b2e-6fa6ab6fa438
-- title:
--   Forest: integral all Branches Boundary Expansion singleton eq prefixed ordered Simplex Integral Aux
-- statement:
--   Terminal one-edge children at any prefixed recursion node are exactly the
--   corresponding prefixed one-edge ordered simplex.
--
--   Source: https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/OrderedAssembly/AllBranches.lean#L959-L975
-- source:
--   https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/OrderedAssembly/AllBranches.lean#L959-L975

import Definitions.Def_BKAR_CubePartition_Support
import Definitions.Def_BKAR_OrderedAssembly_LocalRecursion
import Definitions.Def_BKAR_OrderedAssembly_AllBranches
import Theorems.Thm_BKAR_EdgePath_IsSimplePath_reverse

set_option autoImplicit false
noncomputable section
open BKAR
open BKAR.Forest
variable {V : Type*} [Fintype V] [DecidableEq V]

theorem BKAR.Forest.integral_allBranchesBoundaryExpansion_singleton_eq_prefixed_orderedSimplexIntegralAux
    (choices : ActiveExtensionChoice V)
    (G : Forest V) (e : Edge V)
    (pref : List (Edge V)) (prefixTs : List ℝ)
    (top : ℝ) (ρ : (Edge V → ℝ) → ℝ)
    (hG : G.activeEdges = ∅) :
    (∫ t in 0..top,
        allBranchesBoundaryExpansion choices G.activeEdges.card
          G (pref ++ [e]) (prefixTs ++ [t]) t ρ) =
      orderedSimplexIntegralAux top [e]
        (fun ts => mixedPartialList (pref ++ [e]).reverse ρ
          (G.standardInterp (G.paramsOfOrder (pref ++ [e])
            (prefixTs ++ ts)))) := by sorry
