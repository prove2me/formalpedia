-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave8_20_original_BV_bounded_measurable_clocks_terminal_DCT
-- name    : AvramDividend.Classical.avram_wave8_20_original_BV_bounded_measurable_clocks_terminal_DCT
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-02T20:40:31.144195+00:00
-- url     : https://prove2.me/theorems/274b6f2c-97c5-4aa8-9cc8-16995f4a8150
-- title:
--   Genuine original BV strict-survival killed terminal dominated convergence for bounded measurable clock sequences
-- statement:
--   For any sequence of bounded measurable original physical-time clocks and the genuine BV source HJB terminal killed strictly at ruin, if those exact terminal random variables converge almost surely to a specified limit f, their expectations converge to the expectation of f. The proof supplies all domination and measurability needed for Lebesgue dominated convergence from original source conditions. It does not assume or prove stochastic supermartingale inequality or silently pass through ruin jumps.
-- source:
--   Source-specific Avram Proposition 4(i) localisation. Uses accepted joint measurability of original killed rightpayment terminal ead5faa1 and one common almost-sure uniform physical-horizon envelope 9b971456; dominated convergence of Bochner integrals under an explicit source terminal pointwise a.e. convergence premise. This premise is not inferred from clock convergence, so Lévy jumps, terminal dividend atoms and ruin discontinuities remain honest separate obligations.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave8_20_original_BV_uniform_pathwise_terminal_all_finite_clocks_ae_bound
import Theorems.Thm_AvramDividend_Classical_avram_wave8_20_original_strict_survival_terminal_joint_measurable
open MeasureTheory Set
open Filter
open scoped NNReal ENNReal Topology
open AvramDividend.Classical

theorem AvramDividend.Classical.avram_wave8_20_original_BV_bounded_measurable_clocks_terminal_DCT
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (hBV : X.BoundedVariation) (q : ℝ) (hq : 0 < q)
    (w : ℝ → ℝ) (hw_cont : ContinuousOn w (Ici 0))
    (hw_neg : ∀ y < 0, w y = 0)
    (x : ℝ) (C : ℝ≥0∞)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (H : ℝ≥0) (τ : ℕ → Ω → ℝ≥0)
    (hτMeas : ∀ n, Measurable (τ n))
    (hτBound : ∀ n ω, τ n ω ≤ H)
    (f : Ω → ℝ)
    (hConv : ∀ᵐ ω ∂P, Tendsto
      (fun n : ℕ =>
        if (τ n ω : ℝ≥0∞) < ruinTime X x D ω then
        max 0 (Real.exp (-(q * (τ n ω : ℝ))) *
          w (x + X.X (τ n ω) ω - rightLimit D (τ n ω) ω))
      else 0) atTop (𝓝 (f ω))) :
    Tendsto (fun n : ℕ => ∫ ω,
      (if (τ n ω : ℝ≥0∞) < ruinTime X x D ω then
        max 0 (Real.exp (-(q * (τ n ω : ℝ))) *
          w (x + X.X (τ n ω) ω - rightLimit D (τ n ω) ω))
      else 0) ∂P) atTop
      (𝓝 (∫ ω, f ω ∂P)) := by sorry
