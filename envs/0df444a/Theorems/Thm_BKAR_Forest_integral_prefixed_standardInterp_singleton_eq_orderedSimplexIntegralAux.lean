-- Prove2me | Theorems.Thm_BKAR_Forest_integral_prefixed_standardInterp_singleton_eq_orderedSimplexIntegralAux
-- name    : BKAR.Forest.integral_prefixed_standardInterp_singleton_eq_orderedSimplexIntegralAux
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T09:14:35.014891+00:00
-- url     : https://prove2.me/theorems/195f1337-5750-56c3-9e5f-2a51bdcab641
-- title:
--   Forest: integral prefixed standard Interp singleton eq ordered Simplex Integral Aux
-- statement:
--   The first boundary sector of a prefixed one-edge child is its one-edge ordered
--   simplex integral.
--
--   Source: https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/OrderedAssembly/AllBranches.lean#L825-L837
-- source:
--   https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/OrderedAssembly/AllBranches.lean#L825-L837

import Definitions.Def_BKAR_CubePartition_Support
import Definitions.Def_BKAR_OrderedAssembly_LocalRecursion
import Definitions.Def_BKAR_OrderedAssembly_AllBranches
import Theorems.Thm_BKAR_EdgePath_IsSimplePath_reverse

set_option autoImplicit false
noncomputable section
open BKAR
open BKAR.Forest
variable {V : Type*} [Fintype V] [DecidableEq V]

theorem BKAR.Forest.integral_prefixed_standardInterp_singleton_eq_orderedSimplexIntegralAux
    (G : Forest V) (e : Edge V)
    (pref : List (Edge V)) (prefixTs : List ℝ)
    (top : ℝ) (ρ : (Edge V → ℝ) → ℝ) :
    (∫ t in 0..top,
        mixedPartialList (pref ++ [e]).reverse ρ
          (G.standardInterp (G.paramsOfOrder (pref ++ [e])
            (prefixTs ++ [t])))) =
      orderedSimplexIntegralAux top [e]
        (fun ts => mixedPartialList (pref ++ [e]).reverse ρ
          (G.standardInterp (G.paramsOfOrder (pref ++ [e])
            (prefixTs ++ ts)))) := by sorry
