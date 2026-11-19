-- Prove2me | Theorems.Thm_BilateralProfitMHR_binary_controller_regret_bridge
-- name    : BilateralProfitMHR.binary_controller_regret_bridge
-- status  : Proved
-- author  : @sim2000dg
-- created : 2026-11-18T12:25:26.097989+00:00
-- url     : https://prove2.me/theorems/53736653-3556-4073-a1c0-4f74a2e9ff54
-- title:
--   Finite binary controller realization and expected regret
-- statement:
--   Let a seed-dependent finite binary controller post prices in the unit square, with every fixed-history price measurable in the seed. Its realized posted-price policy is one-bit. For any probability valuation law D, any constant C bounding the expected profit of every controller action, and any comparator with expected profit at most C, the policy regret is at most the expected binary-controller cumulative cost with per-round cost C minus expected profit and trade success probability Ptrade. The controller seed and the iid valuations are independent. The proof identifies the full realized state history, proves the finite binary recursion from the product valuation law, and establishes the conditional expected-profit identity by isolating the current valuation coordinate. No regularity or MHR hypothesis is needed.

import Mathlib
import Definitions.Def_BilateralProfitMHR_Model
import Definitions.Def_BilateralProfitMHR_BinaryControl
open MeasureTheory BilateralProfitMHR BilateralProfit
open scoped ENNReal

theorem BilateralProfitMHR.binary_controller_regret_bridge (T : ℕ) {Ω S : Type} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (D : Measure (ℝ × ℝ)) [IsProbabilityMeasure D]
    (act : Ω → S → ℝ × ℝ) (step : Ω → S → Bool → S) (sinit : Ω → S)
    (hlegal : ∀ ω s, act ω s ∈ unitSq)
    (hmeas : ∀ t (h : Fin t → Bool), Measurable fun ω => act ω (binaryRunState step sinit t h ω)) :
    (controllerPolicy T act step sinit hlegal hmeas).OneBit ∧
    ∀ C : ℝ, (∀ ω s, muP D (act ω s) ≤ C) → ∀ a : ℝ × ℝ, muP D a ≤ C →
      (controllerPolicy T act step sinit hlegal hmeas).regret P D a ≤
        (∫⁻ ω, binaryValue (Ptrade D) (fun x => ENNReal.ofReal (C - muP D x))
          (act ω) (step ω) T (sinit ω) ∂P).toReal := by sorry
