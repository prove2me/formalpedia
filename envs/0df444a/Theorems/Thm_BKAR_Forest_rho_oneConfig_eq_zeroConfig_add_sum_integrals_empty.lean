-- Prove2me | Theorems.Thm_BKAR_Forest_rho_oneConfig_eq_zeroConfig_add_sum_integrals_empty
-- name    : BKAR.Forest.rho_oneConfig_eq_zeroConfig_add_sum_integrals_empty
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T08:34:52.592976+00:00
-- url     : https://prove2.me/theorems/7e526f87-9054-4f8d-872e-e5d96c4e20ce
-- title:
--   Forest: rho one Config eq zero Config add sum integrals empty
-- statement:
--   The true empty-start expansion: the first FTC step runs from the zero
--   configuration to the all-one configuration and differentiates along every
--   edge of the complete graph.
--
--   Source: https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/OrderedExpansion.lean#L443-L499
-- source:
--   https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/OrderedExpansion.lean#L443-L499

import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Definitions.Def_BKAR_ForestGraph
import Definitions.Def_BKAR_Differential
import Definitions.Def_BKAR_OrderedExpansion
set_option autoImplicit false
open BKAR
open BKAR.Forest
variable {V : Type*} [Fintype V] [DecidableEq V]

theorem BKAR.Forest.rho_oneConfig_eq_zeroConfig_add_sum_integrals_empty
    (ρ : (Edge V → ℝ) → ℝ)
    (hρ : ∀ t ∈ Set.uIcc 0 (1 : ℝ),
      DifferentiableAt ℝ ρ (constantConfig t))
    (hint : ∀ e : Edge V,
      IntervalIntegrable
        (fun t : ℝ => partialDeriv e ρ (constantConfig t))
        MeasureTheory.volume 0 1) :
    ρ oneConfig =
      ρ zeroConfig +
        Finset.sum (Finset.univ : Finset (Edge V))
          (fun e => ∫ t in 0..(1 : ℝ),
            partialDeriv e ρ (constantConfig t)) := by sorry
