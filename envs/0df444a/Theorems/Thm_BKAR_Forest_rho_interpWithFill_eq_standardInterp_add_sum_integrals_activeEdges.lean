-- Prove2me | Theorems.Thm_BKAR_Forest_rho_interpWithFill_eq_standardInterp_add_sum_integrals_activeEdges
-- name    : BKAR.Forest.rho_interpWithFill_eq_standardInterp_add_sum_integrals_activeEdges
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T08:26:56.425632+00:00
-- url     : https://prove2.me/theorems/c88d4ee5-b39e-5960-98bd-6bc04b77c170
-- title:
--   Forest: rho interp With Fill eq standard Interp add sum integrals active Edges
-- statement:
--   Boundary-expansion form of the integrated differential identity, with the lower
--   endpoint specialized to the standard interpolation configuration.
--
--   Source: https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/OrderedExpansion.lean#L402-L436
-- source:
--   https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/OrderedExpansion.lean#L402-L436

import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Definitions.Def_BKAR_ForestGraph
import Definitions.Def_BKAR_Differential
import Definitions.Def_BKAR_OrderedExpansion
set_option autoImplicit false
open BKAR
open BKAR.Forest
variable {V : Type*} [Fintype V] [DecidableEq V]

theorem BKAR.Forest.rho_interpWithFill_eq_standardInterp_add_sum_integrals_activeEdges
    (F : Forest V)
    (u : F.EdgeParam → ℝ) (ρ : (Edge V → ℝ) → ℝ) (b : ℝ)
    (hρ : ∀ t ∈ Set.uIcc 0 b,
      DifferentiableAt ℝ ρ (F.interpWithFill u t))
    (hint : ∀ e ∈ F.activeEdges,
      IntervalIntegrable
        (fun t : ℝ => partialDeriv e ρ (F.interpWithFill u t))
        MeasureTheory.volume 0 b) :
    ρ (F.interpWithFill u b) =
      ρ (F.standardInterp u) +
        Finset.sum F.activeEdges
          (fun e => ∫ t in 0..b,
            partialDeriv e ρ (F.interpWithFill u t)) := by sorry
