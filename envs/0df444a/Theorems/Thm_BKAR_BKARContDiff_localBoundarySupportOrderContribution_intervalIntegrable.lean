-- Prove2me | Theorems.Thm_BKAR_BKARContDiff_localBoundarySupportOrderContribution_intervalIntegrable
-- name    : BKAR.BKARContDiff.localBoundarySupportOrderContribution_intervalIntegrable
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T10:05:42.450081+00:00
-- url     : https://prove2.me/theorems/28298f14-14ab-423c-89b5-c49de565a34c
-- title:
--   BKARCont Diff: local Boundary Support Order Contribution interval Integrable
-- statement:
--   The local support/order first-boundary fiber is interval-integrable in its
--   outer upper bound.
--
--   Source: https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/OrderedAssembly/AllBranchesFiberSmoothness.lean#L87-L99
-- source:
--   https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/OrderedAssembly/AllBranchesFiberSmoothness.lean#L87-L99

import Definitions.Def_BKAR_CubePartition_Smoothness
import Definitions.Def_BKAR_OrderedAssembly_AllBranchesFibers
import Definitions.Def_BKAR_OrderedAssembly_AllBranchesFiberSmoothness
set_option autoImplicit false
noncomputable section
open BKAR
open BKAR.BKARContDiff
variable {V : Type*} [Fintype V] [DecidableEq V]
variable {ρ : (Edge V → ℝ) → ℝ}

theorem BKAR.BKARContDiff.localBoundarySupportOrderContribution_intervalIntegrable
    (hρ : BKARContDiff ρ) (choices : Forest.ActiveExtensionChoice V)
    (F : Forest V) (pref : List (Edge V)) (prefixTs : List ℝ)
    (hpref : pref.toFinset = F.edges)
    (hprefixTs : prefixTs.length = pref.length)
    (I : ForestIndex V) (order : List (Edge V)) (a b : ℝ) :
    IntervalIntegrable
      (fun top : ℝ =>
        Forest.localBoundarySupportOrderContribution choices F pref prefixTs
          top I order ρ)
      MeasureTheory.volume a b := by sorry
