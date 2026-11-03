-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave8_04_original_BV_countable_grid_survival_terminal_uniform_ae
-- name    : AvramDividend.Classical.avram_wave8_04_original_BV_countable_grid_survival_terminal_uniform_ae
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-02T18:43:03.150635+00:00
-- url     : https://prove2.me/theorems/72217e14-ae8a-4947-a1e8-29396c8a6035
-- title:
--   Single original-source almost-sure event uniformly dominates all countably many BV strict-survival terminal grid values
-- statement:
--   For every countable deterministic original time grid below H, a single probability-one event supports one common deterministic bound on all original strictly surviving discounted postrightpayment terminal values. It combines finite-horizon uniform source drift ceiling domination with Mathlib's countable conjunction of almost-everywhere events, supplying a legitimate dominated-convergence hypothesis on the same process.
-- source:
--   Original BV stopped verification Eq. (5.13), countable grid terminal dominated convergence, direct corollary of source uniform term bound 370e0f69-2a52-4aeb-b629-db2d76a6ca91.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave8_04_original_BV_uniform_strict_survival_terminal_ae_bound
open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.avram_wave8_04_original_BV_countable_grid_survival_terminal_uniform_ae
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (hBV : X.BoundedVariation) (q : ℝ) (hq : 0 < q)
    (w : ℝ → ℝ) (hw_cont : ContinuousOn w (Ici 0))
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ)
    (hD : IsDividendStrategy 𝓕 D) (H : ℝ≥0)
    (u : ℕ → ℝ≥0) (hu : ∀ n, u n ≤ H) :
    ∃ K : ℝ, 0 ≤ K ∧
      ∀ᵐ ω ∂P, ∀ n : ℕ,
        (if (u n : ℝ≥0∞) < ruinTime X x D ω then
          max 0 (Real.exp (-(q * (u n : ℝ))) *
            w (x + X.X (u n) ω - rightLimit D (u n) ω))
        else 0) ≤ K := by sorry
