-- Prove2me | Theorems.Thm_AvramDividend_Classical_bv_laplace_exponent_positive_magnitude_exact
-- name    : AvramDividend.Classical.bv_laplace_exponent_positive_magnitude_exact
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-04T10:17:33.376575+00:00
-- url     : https://prove2.me/theorems/fb813471-516d-4fba-a228-50c9846cd59e
-- title:
--   Exact canonical BV Lévy–Khintchine exponent in positive jump magnitudes, without extra integrability assumptions
-- statement:
--   For every canonical Classical spectrally negative Lévy process with bounded variation and real theta≥1, the actual Lévy–Khintchine exponent ψ(theta) equals delta*theta minus the real exponential jump-magnitude integral. Bounded variation and the Lévy quadratic moment discharge the compensation and exponential-integrand integrability conditions, and the jump-magnitude pushforward transforms the negative jump integral. This closes the exact stochastic-to-analytic identity required by the positive renewal kernel construction.
-- source:
--   Statement-only early publication to overlap remote verifier latency; the independent helper proof sources remain held until each imported theorem is Proved

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.bv_laplace_exponent_positive_magnitude_exact {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : AvramDividend.Classical.SpectrallyNegativeLevy P 𝓕)
    (hbv : X.BoundedVariation)
    (θ : ℝ) (hθ : 1 ≤ θ) :
    X.ψ θ = X.drift * θ -
      ∫ z : ℝ≥0, (1 - Real.exp (-θ * (z : ℝ)))
        ∂(X.ν.map (fun y : ℝ => Real.toNNReal (-y))) := by
  sorry
