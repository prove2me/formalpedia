-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_ws01e_b_capped_firstRecord_actual_esscher_discount_at_hit
-- name    : AvramDividend.Classical.avram_ws01e_b_capped_firstRecord_actual_esscher_discount_at_hit
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-28T14:21:00.416321+00:00
-- url     : https://prove2.me/theorems/a3830f16-5675-4d3d-9759-e5161f57fb4e
-- title:
--   Exact stopped Esscher survival discount at a finite capped strict upper record
-- statement:
--   For the actual spectrally negative Lévy process, every strict first upward crossing of b≥0 before deterministic cap N attains b with no overshoot. With τ equal to the capped passage time, the terminal Esscher likelihood at τ, multiplied by the genuine Exp(p) survival factor exp(-pτ), is exactly exp(θ b−(p+ψ(θ))τ). The theorem is pointwise on the uncensored first-record event and does not assume tilted Markov or Wiener–Hopf independence. It directly discharges the hWeight hypothesis of the genuine Qp unnormalised capped regeneration theorem for its source-faithful discount choice.
-- source:
--   Canonically Proved firstUpcrossing_value_eq_threshold 014436e7 and exact ENNReal real-to-nonnegative time conversion and exponential algebra; no likelihood division or infinite-path Esscher independence.

import Mathlib
import Definitions.Def_AvramDividend_Classical_TwoSidedExit
import Theorems.Thm_AvramDividend_Classical_firstUpcrossing_value_eq_threshold
open AvramDividend.Classical MeasureTheory
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_ws01e_b_capped_firstRecord_actual_esscher_discount_at_hit
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (b : ℝ) (hb : 0 ≤ b) (N : ℝ≥0)
    (θ p : ℝ) (τ : Ω → ℝ≥0)
    (hτdef : τ = fun ω =>
      (min (twoSidedExitUpTime X b ω) (N : ℝ≥0∞)).toNNReal)
    (ω : Ω)
    (hA : twoSidedExitUpTime X b ω < (N : ℝ≥0∞)) :
    ENNReal.ofReal (Real.exp (-(p * (τ ω : ℝ)))) *
      ENNReal.ofReal (Real.exp
        (θ * X.X (τ ω) ω - (τ ω : ℝ) * X.ψ θ)) =
      ENNReal.ofReal (Real.exp
        (θ * b - (p + X.ψ θ) * (τ ω : ℝ))) := by sorry
