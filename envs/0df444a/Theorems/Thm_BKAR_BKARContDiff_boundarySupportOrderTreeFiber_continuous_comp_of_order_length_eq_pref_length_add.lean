-- Prove2me | Theorems.Thm_BKAR_BKARContDiff_boundarySupportOrderTreeFiber_continuous_comp_of_order_length_eq_pref_length_add
-- name    : BKAR.BKARContDiff.boundarySupportOrderTreeFiber_continuous_comp_of_order_length_eq_pref_length_add
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T09:06:02.055804+00:00
-- url     : https://prove2.me/theorems/8942ce0b-013a-4846-8059-d3f0024d1edd
-- title:
--   BKARCont Diff: boundary Support Order Tree Fiber continuous comp of order length eq pref length add
-- statement:
--   Finite-depth continuity of folded support/order fibers along any recursively
--   generated diagonal parameter-list path.
--
--   Source: https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/OrderedAssembly/AllBranchesFiberSmoothness.lean#L185-L270
-- source:
--   https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/OrderedAssembly/AllBranchesFiberSmoothness.lean#L185-L270

import Definitions.Def_BKAR_CubePartition_Smoothness
import Definitions.Def_BKAR_OrderedAssembly_AllBranchesFibers
import Definitions.Def_BKAR_OrderedAssembly_AllBranchesFiberSmoothness
set_option autoImplicit false
noncomputable section
open BKAR
open BKAR.BKARContDiff
variable {V : Type*} [Fintype V] [DecidableEq V]
variable {ρ : (Edge V → ℝ) → ℝ}

theorem BKAR.BKARContDiff.boundarySupportOrderTreeFiber_continuous_comp_of_order_length_eq_pref_length_add
    (hρ : BKARContDiff ρ) (choices : Forest.ActiveExtensionChoice V) :
    ∀ (k : Nat) (F : Forest V) (pref : List (Edge V))
      {X : Type*} [TopologicalSpace X]
      {tsPath : X → List ℝ} {topPath : X → ℝ},
      BKAR.ListPathContinuous pref.length tsPath →
      Continuous topPath →
      (I : ForestIndex V) → (order : List (Edge V)) →
      order.length = pref.length + k →
      Continuous
        (fun x : X =>
          Forest.boundarySupportOrderTreeFiber choices F pref (tsPath x)
            (topPath x) I order ρ)
  := by sorry
