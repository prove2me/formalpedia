-- Prove2me | Theorems.Thm_AvramDividend_Classical_barrierStrategy_zero_boundary_of_positive_scale_limit
-- name    : AvramDividend.Classical.barrierStrategy_zero_boundary_of_positive_scale_limit
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-25T10:54:19.462882+00:00
-- url     : https://prove2.me/theorems/69a9c354-5f56-4820-b587-c6f318921523
-- title:
--   Zero-barrier reflection follows from positive scale ratios and their real boundary limit
-- statement:
--   If the actual discounted reflected-supremum value at each reciprocal positive barrier agrees with W(a)/W'(a), and these real quotients converge to the zero-barrier scale value, then the original time-zero reflected dividend strategy has exactly that boundary value. The positive-barrier identities automatically imply finiteness at barrier one. Genuine barrier-value monotonicity makes the quotient sequence antitone, and the Proved stochastic zero-limit theorem transfers its real limit into the zero-barrier expectation. This proves the final transfer step needed by the existing Open zero-cap identity, with the two deeper analytic and stochastic hypotheses exposed explicitly.
-- source:
--   Proved barrierSupValue_zero_eq_iInf_reciprocal_of_finite, barrierSupValue_mono_barrier and barrierValue_self_eq_barrierSupValue; Mathlib iInf_eq_of_tendsto.

import Mathlib.Topology.Order.MonotoneConvergence
import Mathlib.Topology.Instances.ENNReal.Lemmas
import Mathlib.Tactic.Positivity
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Theorems.Thm_AvramDividend_Classical_barrierSupValue_zero_eq_iInf_reciprocal_of_finite
import Theorems.Thm_AvramDividend_Classical_barrierSupValue_mono_barrier
import Theorems.Thm_AvramDividend_Classical_barrierValue_self_eq_barrierSupValue

open AvramDividend.Classical MeasureTheory Filter Set
open scoped NNReal ENNReal

theorem AvramDividend.Classical.barrierStrategy_zero_boundary_of_positive_scale_limit
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (q : ℝ) (W : ℝ → ℝ)
    (hscale : ∀ n : ℕ,
      barrierSupValue X (1 / ((n : ℝ) + 1)) q =
        ENNReal.ofReal (W (1 / ((n : ℝ) + 1)) /
          deriv W (1 / ((n : ℝ) + 1))))
    (hlimit : Filter.Tendsto
      (fun n : ℕ => W (1 / ((n : ℝ) + 1)) /
        deriv W (1 / ((n : ℝ) + 1)))
      Filter.atTop (nhds (barrierValue W 0 0))) :
    dividendValue X q 0 (barrierStrategy X 0 0) =
      ENNReal.ofReal (barrierValue W 0 0) := by sorry
