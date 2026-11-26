-- Prove2me | Theorems.Thm_BKAR_Forest_ActiveExtension_singletonGrowth_branchIntegralAux_eq_integral_partialDeriv_interpWithFill_of_activeEdges_eq_empty
-- name    : BKAR.Forest.ActiveExtension.singletonGrowth_branchIntegralAux_eq_integral_partialDeriv_interpWithFill_of_activeEdges_eq_empty
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T08:32:18.655802+00:00
-- url     : https://prove2.me/theorems/d5c7704d-5712-50b1-bb26-b48d3469e617
-- title:
--   Active Extension: singleton Growth branch Integral Aux eq integral partial Deriv interp With Fill of active Edges eq empty
-- statement:
--   The Active Extension construction uses the singleton Growth branch Integral Aux eq integral partial Deriv interp With Fill of active Edges eq empty property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/OrderedTerminal.lean#L39-L53
-- source:
--   https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/OrderedTerminal.lean#L39-L53

import Definitions.Def_BKAR_OrderedBranch
import Definitions.Def_BKAR_OrderedTerminal
set_option autoImplicit false
noncomputable section
open BKAR
open BKAR.Forest
variable {V : Type*} [Fintype V] [DecidableEq V]
open BKAR.Forest.ActiveExtension
variable {F : Forest V} {e : Edge V}

theorem BKAR.Forest.ActiveExtension.singletonGrowth_branchIntegralAux_eq_integral_partialDeriv_interpWithFill_of_activeEdges_eq_empty
    (h : ActiveExtension F e) (top : ℝ) (u : F.EdgeParam → ℝ)
    (ρ : (Edge V → ℝ) → ℝ) (hterm : h.forest.activeEdges = ∅) :
    h.singletonGrowth.branchIntegralAux top u ρ =
      ∫ t in 0..top, partialDeriv e ρ
        (h.forest.interpWithFill (h.extension.extendParam u t) t) := by sorry
