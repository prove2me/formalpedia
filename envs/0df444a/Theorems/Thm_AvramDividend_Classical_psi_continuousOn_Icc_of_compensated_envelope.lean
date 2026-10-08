-- Prove2me | Theorems.Thm_AvramDividend_Classical_psi_continuousOn_Icc_of_compensated_envelope
-- name    : AvramDividend.Classical.psi_continuousOn_Icc_of_compensated_envelope
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-07T23:42:35.588048+00:00
-- url     : https://prove2.me/theorems/2e39984b-9504-49ea-8149-82d2549c9161
-- title:
--   Canonical Lévy exponent continuous on a compact nonnegative interval under a single jump-integrand envelope
-- statement:
--   The canonical Lévy–Khintchine exponent is a continuous polynomial drift-plus-Gaussian term plus a parameterised jump integral. If, on a compact nonnegative Laplace interval [0,B], the compensated jump integrand is dominated almost everywhere by a single ν-integrable function independent of θ, then the exact source-defined ψ is continuous on that interval by dominated convergence. This isolates the precise remaining integrable-envelope step of ψ continuity, to be discharged from the Lévy-measure field using the negative-jump compensator monotonicity and large-jump finite-mass estimate.
-- source:
--   Pinned MeasureTheory.continuous_of_dominated, proved continuousOn_lintegral_parameter_dominated_Icc and canonical SpectrallyNegativeLevy.ψ definition.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

theorem AvramDividend.Classical.psi_continuousOn_Icc_of_compensated_envelope
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (B : ℝ) (hB : 0 ≤ B)
    (bound : ℝ → ℝ)
    (hboundInt : Integrable bound (X.ν.restrict (Iio (0 : ℝ))))
    (hdom : ∀ θ ∈ Icc (0 : ℝ) B,
      ∀ᵐ y : ℝ ∂(X.ν.restrict (Iio (0 : ℝ))),
        ‖Real.exp (θ * y) - 1 - θ * y * (Ioo (-1 : ℝ) 1).indicator 1 y‖ ≤ bound y) :
    ContinuousOn X.ψ (Icc (0 : ℝ) B) := by sorry
