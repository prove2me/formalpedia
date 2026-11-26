-- Prove2me | Theorems.Thm_BKAR_bkar_formula_nonempty
-- name    : BKAR.bkar_formula_nonempty
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T10:08:48.806045+00:00
-- url     : https://prove2.me/theorems/68322712-a2c8-4b21-bc49-f9834943f354
-- title:
--   BKAR: bkar formula nonempty
-- statement:
--   Public scalar BKAR theorem with the empty forest sector split off explicitly
--   as `ρ zeroConfig`.
--
--   Source: https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/Formula.lean#L366-L379
-- source:
--   https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/Formula.lean#L366-L379

import Definitions.Def_BKAR_OrderedAssembly_ForestIndexCube
import Definitions.Def_BKAR_OrderedAssembly_AllBranchesSmoothness
import Definitions.Def_BKAR_Formula
set_option autoImplicit false
noncomputable section
open BKAR
variable {V : Type*} [Fintype V] [DecidableEq V]

theorem BKAR.bkar_formula_nonempty
    (ρ : (Edge V → ℝ) → ℝ)
    (hρ : BKARContDiff ρ) :
    ∀ choices : Forest.ActiveExtensionChoice V,
      ρ oneConfig =
        ρ zeroConfig +
          Finset.sum
            ((Finset.univ : Finset (ForestIndex V)).filter
              (fun I => I.edges ≠ ∅))
            (fun I => Finset.sum (Forest.edgeSetOrders I.edges)
              (fun order =>
                Forest.boundarySupportOrderTreeFiber choices (Forest.empty V)
                  [] [] 1 I order ρ)) := by sorry
