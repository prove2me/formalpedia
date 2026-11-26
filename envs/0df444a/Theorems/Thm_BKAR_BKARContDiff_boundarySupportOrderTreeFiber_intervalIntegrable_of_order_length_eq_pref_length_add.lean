-- Prove2me | Theorems.Thm_BKAR_BKARContDiff_boundarySupportOrderTreeFiber_intervalIntegrable_of_order_length_eq_pref_length_add
-- name    : BKAR.BKARContDiff.boundarySupportOrderTreeFiber_intervalIntegrable_of_order_length_eq_pref_length_add
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T10:05:52.004224+00:00
-- url     : https://prove2.me/theorems/7b8ec651-8a4b-5f4e-8919-ef242825f160
-- title:
--   BKARCont Diff: boundary Support Order Tree Fiber interval Integrable of order length eq pref length add
-- statement:
--   Finite-depth interval-integrability of folded support/order fibers.
--
--   Source: https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/OrderedAssembly/AllBranchesFiberSmoothness.lean#L273-L292
-- source:
--   https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/OrderedAssembly/AllBranchesFiberSmoothness.lean#L273-L292

import Definitions.Def_BKAR_CubePartition_Smoothness
import Definitions.Def_BKAR_OrderedAssembly_AllBranchesFibers
import Definitions.Def_BKAR_OrderedAssembly_AllBranchesFiberSmoothness
set_option autoImplicit false
noncomputable section
open BKAR
open BKAR.BKARContDiff
variable {V : Type*} [Fintype V] [DecidableEq V]
variable {ρ : (Edge V → ℝ) → ℝ}

theorem BKAR.BKARContDiff.boundarySupportOrderTreeFiber_intervalIntegrable_of_order_length_eq_pref_length_add
    (hρ : BKARContDiff ρ) (choices : Forest.ActiveExtensionChoice V)
    (k : Nat) (F : Forest V) (pref : List (Edge V))
    (prefixTs : List ℝ) (I : ForestIndex V) (order : List (Edge V))
    (top : ℝ)
    (hprefixTs : prefixTs.length = pref.length)
    (hlen : order.length = pref.length + k) :
    IntervalIntegrable
      (fun t : ℝ =>
        Forest.boundarySupportOrderTreeFiber choices F pref prefixTs t
          I order ρ)
      MeasureTheory.volume 0 top := by sorry
