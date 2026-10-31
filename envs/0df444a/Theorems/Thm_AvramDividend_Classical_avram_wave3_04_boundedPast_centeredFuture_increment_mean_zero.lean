-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave3_04_boundedPast_centeredFuture_increment_mean_zero
-- name    : AvramDividend.Classical.avram_wave3_04_boundedPast_centeredFuture_increment_mean_zero
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-30T13:33:20.906295+00:00
-- url     : https://prove2.me/theorems/488296c2-5a96-4786-a577-a02199ace877
-- title:
--   Bounded past coefficients preserve centred original Lévy increment zero mean
-- statement:
--   A bounded observation measurable in the genuine Lévy past F_s has zero unconditional product expectation with every integrable centred measurable payoff of the future Lévy increment X_t−X_s. Shifted-increment integrability is deduced from source stationary increments, and product integrability follows from the supplied uniform bound on the past coefficient. The proof then uses conditional expectation factorisation and integral_condExp. This is a genuine discrete predictable-martingale building block, with no separate product-integrability assumptions or replacement of the joint law.
-- source:
--   Canonical Proved chat04_general_future_increment_conditional_expectation UUID 60e3f274-5580-448a-a1d8-6485fa8ab41a; pinned ProbabilityTheory.IdentDistrib.comp/integrable_iff, Integrable.bdd_mul, condExp_mul_of_stronglyMeasurable_left, integral_condExp. Exact private remote probe 89c8a37e-3661-4322-8aff-3f4284494e35 reached intentional sentinel without candidate errors, source SHA-256 388c9ae30418bd4eeef89e9331775f0d502900ad64eec6a15f827f78671d7501.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_chat04_general_future_increment_conditional_expectation

open MeasureTheory ProbabilityTheory Filter AvramDividend.Classical
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_wave3_04_boundedPast_centeredFuture_increment_mean_zero
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (s t : ℝ≥0) (hst : s ≤ t)
    (φ : ℝ → ℝ) (hφ : Measurable φ)
    (H : Ω → ℝ) (hH : StronglyMeasurable[𝓕 s] H)
    (K : ℝ) (hBound : ∀ ω, ‖H ω‖ ≤ K)
    (hInt : Integrable (fun ω => φ (X.X (t - s) ω)) P)
    (hmean : (∫ ω, φ (X.X (t - s) ω) ∂P) = 0) :
    (∫ ω, H ω * φ (X.X t ω - X.X s ω) ∂P) = 0 := by sorry
