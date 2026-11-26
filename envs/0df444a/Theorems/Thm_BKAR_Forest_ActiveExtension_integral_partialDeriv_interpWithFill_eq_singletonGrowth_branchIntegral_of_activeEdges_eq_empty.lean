-- Prove2me | Theorems.Thm_BKAR_Forest_ActiveExtension_integral_partialDeriv_interpWithFill_eq_singletonGrowth_branchIntegral_of_activeEdges_eq_empty
-- name    : BKAR.Forest.ActiveExtension.integral_partialDeriv_interpWithFill_eq_singletonGrowth_branchIntegral_of_activeEdges_eq_empty
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T08:41:26.675462+00:00
-- url     : https://prove2.me/theorems/0345ecb0-27a1-5e04-864b-cb5517eb92db
-- title:
--   Active Extension: integral partial Deriv interp With Fill eq singleton Growth branch Integral of active Edges eq empty
-- statement:
--   The Active Extension construction uses the integral partial Deriv interp With Fill eq singleton Growth branch Integral of active Edges eq empty property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/OrderedTerminal.lean#L73-L80
-- source:
--   https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/OrderedTerminal.lean#L73-L80

import Definitions.Def_BKAR_OrderedBranch
import Definitions.Def_BKAR_OrderedTerminal
set_option autoImplicit false
noncomputable section
open BKAR
open BKAR.Forest
variable {V : Type*} [Fintype V] [DecidableEq V]
open BKAR.Forest.ActiveExtension
variable {F : Forest V} {e : Edge V}

theorem BKAR.Forest.ActiveExtension.integral_partialDeriv_interpWithFill_eq_singletonGrowth_branchIntegral_of_activeEdges_eq_empty
    (h : ActiveExtension F e) (u : F.EdgeParam → ℝ)
    (ρ : (Edge V → ℝ) → ℝ) (hterm : h.forest.activeEdges = ∅) :
    (∫ t in 0..(1 : ℝ), partialDeriv e ρ
        (h.forest.interpWithFill (h.extension.extendParam u t) t)) =
      h.singletonGrowth.branchIntegral u ρ := by sorry
