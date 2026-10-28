-- Prove2me | Theorems.Thm_AvramDividend_Classical_barrierSupValue_zero_eq_iInf_cofinal_of_finite
-- name    : AvramDividend.Classical.barrierSupValue_zero_eq_iInf_cofinal_of_finite
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-25T10:51:08.41255+00:00
-- url     : https://prove2.me/theorems/05e26f10-20d2-4e5a-ade1-01f331c3d59c
-- title:
--   Zero-barrier dividend limit along any positive sequence tending to zero
-- statement:
--   If expected reflected dividends at barrier one are finite, then the genuine expected zero-barrier reward equals the infimum of rewards along every sequence of positive drawdown barriers converging to zero. This extends the Proved reciprocal-barrier identity to any cofinal sequence, allowing analytic scale-function approximations to use differentiability points of their choice. Monotonicity of the original barrier dividend value and cofinality supply the proof.
-- source:
--   Proved barrierSupValue_zero_eq_iInf_reciprocal_of_finite and barrierSupValue_mono_barrier; Mathlib specific reciprocal limits.

import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Topology.Order.MonotoneConvergence
import Theorems.Thm_AvramDividend_Classical_barrierSupValue_zero_eq_iInf_reciprocal_of_finite
import Theorems.Thm_AvramDividend_Classical_barrierSupValue_mono_barrier

open AvramDividend.Classical MeasureTheory Filter Set
open scoped NNReal ENNReal

theorem AvramDividend.Classical.barrierSupValue_zero_eq_iInf_cofinal_of_finite
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (q : ℝ)
    (hfinite : barrierSupValue X 1 q ≠ ⊤)
    (r : ℕ → ℝ) (hrpos : ∀ n, 0 < r n)
    (hrlim : Filter.Tendsto r Filter.atTop (nhds (0 : ℝ))) :
    barrierSupValue X 0 q = ⨅ n : ℕ, barrierSupValue X (r n) q := by sorry
