-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave8_20_original_BV_bounded_random_clock_survival_terminal_ae_bound
-- name    : AvramDividend.Classical.avram_wave8_20_original_BV_bounded_random_clock_survival_terminal_ae_bound
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-02T18:54:29.879766+00:00
-- url     : https://prove2.me/theorems/2563fd4a-7f18-48ae-8052-ec0cbc0a1798
-- title:
--   Common almost-sure compact BV survival terminal bound evaluated at any bounded random clock
-- statement:
--   For the actual Standing BV spectrally negative Levy process and admissible dividend strategy, every random nonnegative clock bounded by a finite deterministic horizon has a discounted positive-part post-rightpayment strict-survival terminal bounded by a deterministic finite constant almost surely. The same almost-sure event works when the bounded random time is substituted, without requiring clock measurability or a stopping-time predicate. This supports source localisation and dominated convergence independently of the stochastic supermartingale budget.
-- source:
--   Avram Proposition 4(i), original stopped BV verification. Exact source drift ceiling and strict pre-ruin postpayment solvency. A single almost-sure pathwise horizon event remains valid at a random stopping clock, strengthening per-deterministic-time a.e. domination without the desired supermartingale inequality.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_bv_standing_drift_pos
import Theorems.Thm_AvramDividend_Classical_avram_wave7_02_original_BV_postpayment_deterministic_horizon_upper_strip
import Theorems.Thm_AvramDividend_Classical_continuous_test_abs_le_on_finite_cap
import Theorems.Thm_AvramDividend_Classical_postPaymentReserve_nonnegative_strictly_before_ruin
open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.avram_wave8_20_original_BV_bounded_random_clock_survival_terminal_ae_bound
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (hBV : X.BoundedVariation) (q : ℝ) (hq : 0 < q)
    (w : ℝ → ℝ) (hw_cont : ContinuousOn w (Ici 0))
    (x : ℝ) (C : ℝ≥0∞)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (H : ℝ≥0) (τ : Ω → ℝ≥0) (hτ : ∀ ω, τ ω ≤ H) :
    ∃ K : ℝ, 0 ≤ K ∧
      ∀ᵐ ω ∂P,
        (if (τ ω : ℝ≥0∞) < ruinTime X x D ω then
          max 0 (Real.exp (-(q * (τ ω : ℝ))) *
            w (x + X.X (τ ω) ω - rightLimit D (τ ω) ω))
        else 0) ≤ K := by sorry
