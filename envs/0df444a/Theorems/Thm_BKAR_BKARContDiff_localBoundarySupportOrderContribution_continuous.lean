-- Prove2me | Theorems.Thm_BKAR_BKARContDiff_localBoundarySupportOrderContribution_continuous
-- name    : BKAR.BKARContDiff.localBoundarySupportOrderContribution_continuous
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T09:19:56.016926+00:00
-- url     : https://prove2.me/theorems/68f0af76-73b7-4836-b0fc-b62ee25a6608
-- title:
--   BKARCont Diff: local Boundary Support Order Contribution continuous
-- statement:
--   The local support/order first-boundary fiber is continuous as a function of
--   its outer upper bound.
--
--   Source: https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/OrderedAssembly/AllBranchesFiberSmoothness.lean#L27-L81
-- source:
--   https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/OrderedAssembly/AllBranchesFiberSmoothness.lean#L27-L81

import Definitions.Def_BKAR_CubePartition_Smoothness
import Definitions.Def_BKAR_OrderedAssembly_AllBranchesFibers
import Definitions.Def_BKAR_OrderedAssembly_AllBranchesFiberSmoothness
set_option autoImplicit false
noncomputable section
open BKAR
open BKAR.BKARContDiff
variable {V : Type*} [Fintype V] [DecidableEq V]
variable {ρ : (Edge V → ℝ) → ℝ}

theorem BKAR.BKARContDiff.localBoundarySupportOrderContribution_continuous
    (hρ : BKARContDiff ρ) (choices : Forest.ActiveExtensionChoice V)
    (F : Forest V) (pref : List (Edge V)) (prefixTs : List ℝ)
    (hpref : pref.toFinset = F.edges)
    (hprefixTs : prefixTs.length = pref.length)
    (I : ForestIndex V) (order : List (Edge V)) :
    Continuous
      (fun top : ℝ =>
        Forest.localBoundarySupportOrderContribution choices F pref prefixTs
          top I order ρ) := by sorry
