-- Prove2me | Theorems.Thm_BKAR_Forest_ActiveExtension_singletonGrowth_branchIntegral_eq_integral_partialDeriv_interpWithFill_of_activeEdges_eq_empty
-- name    : BKAR.Forest.ActiveExtension.singletonGrowth_branchIntegral_eq_integral_partialDeriv_interpWithFill_of_activeEdges_eq_empty
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T08:33:30.018353+00:00
-- url     : https://prove2.me/theorems/ee06763e-3081-4f9e-886c-c77bd820f579
-- title:
--   Active Extension: singleton Growth branch Integral eq integral partial Deriv interp With Fill of active Edges eq empty
-- statement:
--   The Active Extension construction uses the singleton Growth branch Integral eq integral partial Deriv interp With Fill of active Edges eq empty property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/OrderedTerminal.lean#L64-L71
-- source:
--   https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/OrderedTerminal.lean#L64-L71

import Definitions.Def_BKAR_OrderedBranch
import Definitions.Def_BKAR_OrderedTerminal
set_option autoImplicit false
noncomputable section
open BKAR
open BKAR.Forest
variable {V : Type*} [Fintype V] [DecidableEq V]
open BKAR.Forest.ActiveExtension
variable {F : Forest V} {e : Edge V}

theorem BKAR.Forest.ActiveExtension.singletonGrowth_branchIntegral_eq_integral_partialDeriv_interpWithFill_of_activeEdges_eq_empty
    (h : ActiveExtension F e) (u : F.EdgeParam → ℝ)
    (ρ : (Edge V → ℝ) → ℝ) (hterm : h.forest.activeEdges = ∅) :
    h.singletonGrowth.branchIntegral u ρ =
      ∫ t in 0..(1 : ℝ), partialDeriv e ρ
        (h.forest.interpWithFill (h.extension.extendParam u t) t) := by sorry
