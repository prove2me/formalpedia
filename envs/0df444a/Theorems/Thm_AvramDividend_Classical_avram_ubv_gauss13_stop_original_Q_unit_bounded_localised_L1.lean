-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_ubv_gauss13_stop_original_Q_unit_bounded_localised_L1
-- name    : AvramDividend.Classical.avram_ubv_gauss13_stop_original_Q_unit_bounded_localised_L1
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-08T22:59:28.683956+00:00
-- url     : https://prove2.me/theorems/59e1e063-c667-42b3-826e-d4aa3df50199
-- title:
--   Original quadratic Gaussian physical-clock L1 limit with unit-bounded localised multipliers
-- statement:
--   Necessary bounded predictable-coefficient passage for a338c453-58c0-411c-aaca-5cec689ed807 finite-cap physical C2 Gaussian reward ledger and 249c532d-4ec0-498c-81f0-b380dd476344 top cap. For the same original process X.X, represent each ceiling Q(T_n) as conditional expectation of one fixed integrable terminal original Gaussian compensated square Q(B) using Proved 6258d525; Proved d39c5abe supplies almost-everywhere physical-clock convergence. For compact-localised, unit-bounded, a.e. convergent measurable coefficients G_n, show the weighted original source G_n Q(T_n) converges to G Q(sigma) in L1 by uniform integrability. An arbitrary finite uniform bound C can be normalised to 1. Stopped history measurability and original F0 centring of actual finite predictable cells still follow from 4a4b4e27 and 6242d57f; this theorem provides analytic L1 passage only. No independent Brownian process and no floor-clock stopping hypothesis.

import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy

open MeasureTheory Filter AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_ubv_gauss13_stop_original_Q_unit_bounded_localised_L1
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hν : X.ν = 0)
    (Q : ℝ≥0 → Ω → ℝ)
    (hQsource : ∀ t ω, Q t ω =
      (X.X t ω - (t : ℝ) * X.c) ^ 2 - (t : ℝ) * X.σ ^ 2)
    (B : ℝ≥0) (hQB : Integrable (Q B) P)
    (σ : Ω → ℝ≥0) (T : ℕ → Ω → ℝ≥0)
    (ℋ : ℕ → MeasurableSpace Ω)
    (hℋ : ∀ n, ℋ n ≤ mΩ)
    (hCE : ∀ n, (fun ω => Q (T n ω) ω) =ᵐ[P]
      condExp (ℋ n) P (Q B))
    (hAE : ∀ᵐ ω ∂P,
      Tendsto (fun n => Q (T n ω) ω) atTop
        (nhds (Q (σ ω) ω)))
    (G : ℕ → Ω → ℝ) (g : Ω → ℝ)
    (hGmeas : ∀ n, AEStronglyMeasurable (G n) P)
    (hGunit : ∀ n ω, ‖G n ω‖ ≤ 1)
    (hGae : ∀ᵐ ω ∂P, Tendsto (fun n => G n ω) atTop (nhds (g ω))) :
    Tendsto (fun n =>
      eLpNorm (fun ω => G n ω * Q (T n ω) ω -
        g ω * Q (σ ω) ω) 1 P)
      atTop (nhds 0) := by
  sorry
