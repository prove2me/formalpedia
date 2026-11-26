-- Prove2me | Theorems.Thm_BKAR_Forest_ActiveBranchData_singleton_branchIntegralAux_eq_sum_integrals_partialDeriv_interpWithFill_of_activeEdges_eq_empty
-- name    : BKAR.Forest.ActiveBranchData.singleton_branchIntegralAux_eq_sum_integrals_partialDeriv_interpWithFill_of_activeEdges_eq_empty
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T08:36:30.560054+00:00
-- url     : https://prove2.me/theorems/336b45c9-46ae-5938-bd12-c423e922b02f
-- title:
--   Active Branch Data: singleton branch Integral Aux eq sum integrals partial Deriv interp With Fill of active Edges eq empty
-- statement:
--   Terminal singleton branches turn the active-edge branch sum into the sum of
--   one-edge partial-derivative integrals on the terminal fill-parameter
--   interpolations.
--
--   Source: https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/OrderedRemainder.lean#L174-L190
-- source:
--   https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/OrderedRemainder.lean#L174-L190

import Definitions.Def_BKAR_OrderedRecursion
import Definitions.Def_BKAR_OrderedRemainder
set_option autoImplicit false
noncomputable section
open BKAR
open BKAR.Forest
variable {V : Type*} [Fintype V] [DecidableEq V]
open BKAR.Forest.ActiveBranchData
variable {F : Forest V}

theorem BKAR.Forest.ActiveBranchData.singleton_branchIntegralAux_eq_sum_integrals_partialDeriv_interpWithFill_of_activeEdges_eq_empty
    (extensions : ∀ e : {e // e ∈ F.activeEdges},
      ActiveExtension F e.val)
    (top : ℝ) (u : F.EdgeParam → ℝ) (ρ : (Edge V → ℝ) → ℝ)
    (hterm : ∀ e : {e // e ∈ F.activeEdges},
      (extensions e).forest.activeEdges = ∅) :
    (singleton extensions).branchIntegralAux top u ρ =
      Finset.sum F.activeEdges.attach
        (fun e => ∫ t in 0..top,
          partialDeriv e.val ρ
            ((extensions e).forest.interpWithFill
              ((extensions e).extension.extendParam u t) t)) := by sorry
