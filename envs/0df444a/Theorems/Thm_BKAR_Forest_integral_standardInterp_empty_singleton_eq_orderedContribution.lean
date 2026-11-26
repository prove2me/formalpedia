-- Prove2me | Theorems.Thm_BKAR_Forest_integral_standardInterp_empty_singleton_eq_orderedContribution
-- name    : BKAR.Forest.integral_standardInterp_empty_singleton_eq_orderedContribution
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T08:59:09.792102+00:00
-- url     : https://prove2.me/theorems/2a0ca3d4-0f98-4377-8b61-850616a7b690
-- title:
--   Forest: integral standard Interp empty singleton eq ordered Contribution
-- statement:
--   The first boundary sector of any one-edge child from the empty forest is the
--   corresponding one-edge ordered contribution. No terminality is needed here.
--
--   Source: https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/OrderedAssembly/AllBranches.lean#L843-L849
-- source:
--   https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/OrderedAssembly/AllBranches.lean#L843-L849

import Definitions.Def_BKAR_CubePartition_Support
import Definitions.Def_BKAR_OrderedAssembly_LocalRecursion
import Definitions.Def_BKAR_OrderedAssembly_AllBranches
import Theorems.Thm_BKAR_EdgePath_IsSimplePath_reverse

set_option autoImplicit false
noncomputable section
open BKAR
open BKAR.Forest
variable {V : Type*} [Fintype V] [DecidableEq V]

theorem BKAR.Forest.integral_standardInterp_empty_singleton_eq_orderedContribution
    (G : Forest V) (e : Edge V) (ρ : (Edge V → ℝ) → ℝ) :
    (∫ t in 0..(1 : ℝ),
        mixedPartialList [e].reverse ρ
          (G.standardInterp (G.paramsOfOrder [e] [t]))) =
      G.orderedContribution [e] ρ := by sorry
