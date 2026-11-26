-- Prove2me | Theorems.Thm_BKAR_Forest_sum_integrals_activeEdges_eq_sum_activeExtensions
-- name    : BKAR.Forest.sum_integrals_activeEdges_eq_sum_activeExtensions
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T08:29:24.7613+00:00
-- url     : https://prove2.me/theorems/3d36fd09-b6ab-5a3e-a72e-a7d59ae05c95
-- title:
--   Forest: sum integrals active Edges eq sum active Extensions
-- statement:
--   Rewrite the active-edge remainder as a sum over explicitly chosen one-edge
--   forest extensions.
--
--   Source: https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/OrderedExpansion.lean#L586-L608
-- source:
--   https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/OrderedExpansion.lean#L586-L608

import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Definitions.Def_BKAR_ForestGraph
import Definitions.Def_BKAR_Differential
import Definitions.Def_BKAR_OrderedExpansion
set_option autoImplicit false
open BKAR
open BKAR.Forest
variable {V : Type*} [Fintype V] [DecidableEq V]

theorem BKAR.Forest.sum_integrals_activeEdges_eq_sum_activeExtensions
    (F : Forest V)
    (es : List (Edge V)) (u : F.EdgeParam → ℝ)
    (ρ : (Edge V → ℝ) → ℝ) (a b : ℝ)
    (hbound : ∀ t ∈ Set.uIcc a b, ∀ e : F.EdgeParam, t ≤ u e)
    (extensions : ∀ e : {e // e ∈ F.activeEdges},
      ActiveExtension F e.val) :
    Finset.sum F.activeEdges
      (fun e => ∫ t in a..b,
        mixedPartialList (e :: es) ρ (F.interpWithFill u t)) =
      Finset.sum F.activeEdges.attach
        (fun e => ∫ t in a..b,
          mixedPartialList (e.val :: es) ρ
            ((extensions e).forest.interpWithFill
              ((extensions e).extension.extendParam u t) t)) := by sorry
