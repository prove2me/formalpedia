-- Prove2me | Theorems.Thm_BKAR_Forest_mixedPartialList_interpWithFill_eq_standardInterp_add_sum_singletonBranchIntegrals_standardInterp_of_activeEdges_eq_empty
-- name    : BKAR.Forest.mixedPartialList_interpWithFill_eq_standardInterp_add_sum_singletonBranchIntegrals_standardInterp_of_activeEdges_eq_empty
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T09:22:06.411497+00:00
-- url     : https://prove2.me/theorems/0b6dbdc3-b167-4bc2-9181-5004ef82abb8
-- title:
--   Forest: mixed Partial List interp With Fill eq standard Interp add sum singleton Branch Integrals standard Interp of active Edges eq empty
-- statement:
--   Terminal active-extension expansion rewritten directly as standard
--   singleton-branch integrals.
--
--   Source: https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/OrderedRemainder.lean#L415-L441
-- source:
--   https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/OrderedRemainder.lean#L415-L441

import Definitions.Def_BKAR_OrderedRecursion
import Definitions.Def_BKAR_OrderedRemainder
set_option autoImplicit false
noncomputable section
open BKAR
open BKAR.Forest
variable {V : Type*} [Fintype V] [DecidableEq V]

theorem BKAR.Forest.mixedPartialList_interpWithFill_eq_standardInterp_add_sum_singletonBranchIntegrals_standardInterp_of_activeEdges_eq_empty
    (F : Forest V)
    (es : List (Edge V)) (u : F.EdgeParam → ℝ)
    (ρ : (Edge V → ℝ) → ℝ) (b : ℝ)
    (hbound : ∀ t ∈ Set.uIcc 0 b, ∀ e : F.EdgeParam, t ≤ u e)
    (hρ : ∀ t ∈ Set.uIcc 0 b,
      DifferentiableAt ℝ (mixedPartialList es ρ) (F.interpWithFill u t))
    (hint : ∀ e ∈ F.activeEdges,
      IntervalIntegrable
        (fun t : ℝ => mixedPartialList (e :: es) ρ
          (F.interpWithFill u t))
        MeasureTheory.volume 0 b)
    (extensions : ∀ e : {e // e ∈ F.activeEdges},
      ActiveExtension F e.val)
    (hterm : ∀ e : {e // e ∈ F.activeEdges},
      (extensions e).forest.activeEdges = ∅) :
    mixedPartialList es ρ (F.interpWithFill u b) =
      mixedPartialList es ρ (F.standardInterp u) +
        Finset.sum F.activeEdges.attach
          (fun e => ∫ t in 0..b,
            mixedPartialList (e.val :: es) ρ
              ((extensions e).forest.standardInterp
                ((extensions e).extension.extendParam u t))) := by sorry
