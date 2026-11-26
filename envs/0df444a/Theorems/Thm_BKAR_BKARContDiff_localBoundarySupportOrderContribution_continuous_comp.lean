-- Prove2me | Theorems.Thm_BKAR_BKARContDiff_localBoundarySupportOrderContribution_continuous_comp
-- name    : BKAR.BKARContDiff.localBoundarySupportOrderContribution_continuous_comp
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T09:19:51.229886+00:00
-- url     : https://prove2.me/theorems/a459d536-b5f0-5c90-bd1a-d97e4bbd32ff
-- title:
--   BKARCont Diff: local Boundary Support Order Contribution continuous comp
-- statement:
--   The local support/order first-boundary fiber is continuous along any
--   fixed-length coordinatewise-continuous parameter-list path.
--
--   Source: https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/OrderedAssembly/AllBranchesFiberSmoothness.lean#L105-L179
-- source:
--   https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/OrderedAssembly/AllBranchesFiberSmoothness.lean#L105-L179

import Definitions.Def_BKAR_CubePartition_Smoothness
import Definitions.Def_BKAR_OrderedAssembly_AllBranchesFibers
import Definitions.Def_BKAR_OrderedAssembly_AllBranchesFiberSmoothness
set_option autoImplicit false
noncomputable section
open BKAR
open BKAR.BKARContDiff
variable {V : Type*} [Fintype V] [DecidableEq V]
variable {ρ : (Edge V → ℝ) → ℝ}

theorem BKAR.BKARContDiff.localBoundarySupportOrderContribution_continuous_comp
    (hρ : BKARContDiff ρ) (choices : Forest.ActiveExtensionChoice V)
    (F : Forest V) (pref : List (Edge V))
    {X : Type*} [TopologicalSpace X]
    {tsPath : X → List ℝ} {topPath : X → ℝ}
    (hts : BKAR.ListPathContinuous pref.length tsPath)
    (htop : Continuous topPath)
    (I : ForestIndex V) (order : List (Edge V)) :
    Continuous
      (fun x : X =>
        Forest.localBoundarySupportOrderContribution choices F pref
          (tsPath x) (topPath x) I order ρ) := by sorry
