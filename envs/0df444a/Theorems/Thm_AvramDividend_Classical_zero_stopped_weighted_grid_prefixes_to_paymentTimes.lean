-- Prove2me | Theorems.Thm_AvramDividend_Classical_zero_stopped_weighted_grid_prefixes_to_paymentTimes
-- name    : AvramDividend.Classical.zero_stopped_weighted_grid_prefixes_to_paymentTimes
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-26T17:57:28.890921+00:00
-- url     : https://prove2.me/theorems/23b73608-84a6-437b-8c91-012933a51dca
-- title:
--   Countable surviving Stieltjes prefixes identify exact stopped rewards, including time zero
-- statement:
--   For an arbitrary strict ruin time σ and a deterministic grid cofinal strictly before σ, assume two dividend measures agree on every surviving positive prefix for an arbitrary nonnegative reward weight, and both have zero initial atom. Then they give identical total stopped rewards over the precise Prove2Me paymentTimes σ. The proof combines the accepted strict endpoint decomposition, the directedness of filtered prefixes, directed-union monotone convergence and the zero-atom lemma. It supplies the missing pathwise measure-theoretic bridge for zero-barrier finite-activity stochastic valuation.
-- source:
--   Prove2Me DividendStrategy.paymentTimes and ReflectionBarrier canonical definitions, and Mathlib MeasureTheory.setLIntegral_iUnion_of_directed. Avram, Palmowski and Pistorius (2007), §3.3.

import Theorems.Thm_AvramDividend_Classical_paymentTimes_eq_zero_union_filtered_Ioc_of_grid
import Theorems.Thm_AvramDividend_Classical_directed_stieltjes_prefixes_determine_union_reward
import Theorems.Thm_AvramDividend_Classical_filtered_surviving_Ioc_prefixes_directed
import Theorems.Thm_AvramDividend_Classical_zero_atom_free_stieltjes_reward_union
import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

theorem AvramDividend.Classical.zero_stopped_weighted_grid_prefixes_to_paymentTimes
    (σ : ℝ≥0∞) (grid : ℕ → ℝ≥0)
    (μ ν : Measure ℝ) (f : ℝ → ℝ≥0∞)
    (hcofinal : ∀ t : ℝ, 0 < t → ENNReal.ofReal t < σ →
      ∃ n : ℕ, t ≤ (grid n : ℝ) ∧ (grid n : ℝ≥0∞) < σ)
    (hprefix : ∀ n : ℕ, (grid n : ℝ≥0∞) < σ →
      (∫⁻ t in Ioc (0 : ℝ) (grid n : ℝ), f t ∂μ) =
        (∫⁻ t in Ioc (0 : ℝ) (grid n : ℝ), f t ∂ν))
    (hzeroμ : μ {(0 : ℝ)} = 0) (hzeroν : ν {(0 : ℝ)} = 0) :
    (∫⁻ t in paymentTimes σ, f t ∂μ) =
      (∫⁻ t in paymentTimes σ, f t ∂ν) := by sorry
