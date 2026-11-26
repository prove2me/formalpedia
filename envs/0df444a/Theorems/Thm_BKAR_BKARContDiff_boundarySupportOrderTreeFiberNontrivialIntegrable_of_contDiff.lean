-- Prove2me | Theorems.Thm_BKAR_BKARContDiff_boundarySupportOrderTreeFiberNontrivialIntegrable_of_contDiff
-- name    : BKAR.BKARContDiff.boundarySupportOrderTreeFiberNontrivialIntegrable_of_contDiff
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T09:20:18.301734+00:00
-- url     : https://prove2.me/theorems/4de615cf-0e1d-4c01-9baa-fc621a09ac01
-- title:
--   BKARCont Diff: boundary Support Order Tree Fiber Nontrivial Integrable of cont Diff
-- statement:
--   The narrowed nontrivial support/order fiber-integrability predicate follows
--   from global `C^∞` smoothness.
--
--   Source: https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/OrderedAssembly/AllBranchesFiberSmoothness.lean#L298-L337
-- source:
--   https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/OrderedAssembly/AllBranchesFiberSmoothness.lean#L298-L337

import Definitions.Def_BKAR_CubePartition_Smoothness
import Definitions.Def_BKAR_OrderedAssembly_AllBranchesFibers
import Definitions.Def_BKAR_OrderedAssembly_AllBranchesFiberSmoothness
set_option autoImplicit false
noncomputable section
open BKAR
open BKAR.BKARContDiff
variable {V : Type*} [Fintype V] [DecidableEq V]
variable {ρ : (Edge V → ℝ) → ℝ}

theorem BKAR.BKARContDiff.boundarySupportOrderTreeFiberNontrivialIntegrable_of_contDiff
    (hρ : BKARContDiff ρ) (choices : Forest.ActiveExtensionChoice V) :
    ∀ (n : Nat) (F : Forest V) (pref : List (Edge V))
      (prefixTs : List ℝ) (top : ℝ),
      prefixTs.length = pref.length →
      Forest.boundarySupportOrderTreeFiberNontrivialIntegrable choices n
        F pref prefixTs top ρ
  := by sorry
