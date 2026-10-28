-- Prove2me | Theorems.Thm_AvramDividend_Classical_bv_stopped_scale_ost_payoff_balance
-- name    : AvramDividend.Classical.bv_stopped_scale_ost_payoff_balance
-- status  : Open
-- author  : @WillR
-- created : 2026-10-26T16:33:12.686181+00:00
-- url     : https://prove2.me/theorems/09caed2c-1cc0-4083-8a24-a39b70d511c8
-- title:
--   Bounded-variation stopped-scale optional-stopping payoff balance
-- statement:
--   Optional-stopping payoff balance for the bounded-variation stopped scale martingale: the factored two-sided exit payoff integral (discount times ofReal (W a) on strict up-exit first, zero otherwise, in twoSidedExit wrapper form) equals ofReal (W x). This is the precise open gap hOST isolated in the 2bb529c8 repair line: it follows from the BV stopped-scale martingale 5955d9a2-224d-4fe7-acf9-fc1fbb015da5 plus no-creeping-ae 43a28d8e-14f3-44d6-8b46-347138818c52 with scale-function vanishing on negatives, via a discrete (Nat-indexed) dominated-convergence limit using MeasureTheory.tendsto_lintegral_of_dominated_convergence. It assumes no Open exit theorem and has no return edge to 2bb529c8-d611-4c49-9460-1d4af4620ae8, whose proof will cite it; hence for the 09663d0d case split and the barrier_strategy_value chain.
-- source:
--   Isolated as the exact hOST gap in repair iteration G of parent CE 16067 for AvramDividend.Classical.bounded_variation_stopped_scale_balance (2bb529c8-d611-4c49-9460-1d4af4620ae8) within mission 1300fbe7-ca8c-49f9-a4de-4cb35ebd2f43; upstream foundations are Open 5955d9a2 (BV stopped-scale martingale) and Open 43a28d8e (BV no-creeping-ae), both verified acyclic.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Definitions.Def_AvramDividend_Classical_TwoSidedExit
open AvramDividend.Classical MeasureTheory Set Filter Topology
open scoped NNReal ENNReal

theorem AvramDividend.Classical.bv_stopped_scale_ost_payoff_balance
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (q : ℝ) (hq : 0 < q)
    (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (hBV : X.BoundedVariation)
    (a x : ℝ) (ha : 0 < a) (hx0 : 0 ≤ x) (hxa : x ≤ a) :
    (∫⁻ ω, if twoSidedExitUpTime X (a - x) ω < twoSidedExitDownTime X (-x) ω then
      ENNReal.ofReal (Real.exp (-(q * (twoSidedExitUpTime X (a - x) ω).toReal))) *
        ENNReal.ofReal (W a)
    else 0 ∂P) = ENNReal.ofReal (W x) := by sorry
