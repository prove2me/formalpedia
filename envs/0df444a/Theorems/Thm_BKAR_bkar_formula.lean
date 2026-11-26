-- Prove2me | Theorems.Thm_BKAR_bkar_formula
-- name    : BKAR.bkar_formula
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T10:07:46.141259+00:00
-- url     : https://prove2.me/theorems/1dd9ca1b-2325-5d82-a6db-61d694db92c4
-- title:
--   BKAR: bkar formula
-- statement:
--   Public scalar BKAR theorem. The statement is uniform in the auxiliary
--   forest-extension choices made by the ordered assembly.
--
--   Source: https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/Formula.lean#L261-L270
-- source:
--   https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/Formula.lean#L261-L270

import Definitions.Def_BKAR_OrderedAssembly_ForestIndexCube
import Definitions.Def_BKAR_OrderedAssembly_AllBranchesSmoothness
import Definitions.Def_BKAR_Formula
set_option autoImplicit false
noncomputable section
open BKAR
variable {V : Type*} [Fintype V] [DecidableEq V]

theorem BKAR.bkar_formula
    (ρ : (Edge V → ℝ) → ℝ)
    (hρ : BKARContDiff ρ) :
    ∀ choices : Forest.ActiveExtensionChoice V,
      ρ oneConfig =
        Finset.sum (Finset.univ : Finset (ForestIndex V))
          (fun I => Finset.sum (Forest.edgeSetOrders I.edges)
            (fun order =>
              Forest.rootBoundarySupportOrderContribution choices ρ I order)) := by sorry
