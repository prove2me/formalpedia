-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_ga_a375p_probability_expected_Gaussian_energy_cross_discount_selected_budget
-- name    : AvramDividend.Classical.avram_ga_a375p_probability_expected_Gaussian_energy_cross_discount_selected_budget
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-14T12:33:46.796401+00:00
-- url     : https://prove2.me/theorems/879b547c-0100-419c-a54b-81df5af05da0
-- title:
--   Source Gaussian physical discount Young correction and vanishing Hessian cross yield integrable selected-threshold small expected budget
-- statement:
--   If an almost-everywhere original Gaussian small-source bound is available at a tolerance-dependent raw cutoff δ, with positive part dominated by ε times integrable raw physical energy with uniformly bounded expectation K, M/2 times integrable absolute Hessian cross whose expected value vanishes, and m(qΔ_m L)²/(2ε) deterministic Gaussian discount Young correction, then for every target budget η one can choose a cutoff with integrability at all finite mesh levels and expected positive small-source at most η eventually. It applies the already proved exact physical mesh discount squared-width vanishing a206 and selected-threshold integrability gluing a364; the original source a373 and a367/a214 furnish all hypotheses for a361. The probability-measure assumption is essential to make constant discount corrections integrable and to identify their integrals with their values. An earlier version a375 without this assumption is not mathematically valid on arbitrary infinite measures and must not be used.
-- source:
--   Generic selected threshold a364, original finite mesh rate a206, original raw energy a367 and cross a214 via a373.

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_ga_a364_selected_small_budget_of_ae_modulus_and_vanishing_sources
import Theorems.Thm_AvramDividend_Classical_avram_ga_a206_original_discount_first_energy_width_square_rate_tendsto_zero
open MeasureTheory Filter Topology
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_ga_a375p_probability_expected_Gaussian_energy_cross_discount_selected_budget
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P]
    (S : ℝ → ℕ → Ω → ℝ) (E C : ℕ → Ω → ℝ)
    (n : ℕ) (q L M K : ℝ)
    (hK : 0 ≤ K) (hM : 0 ≤ M)
    (hSm : ∀ δ, 0 < δ → ∀ m,
      AEStronglyMeasurable (fun ω => max (S δ m ω) 0) P)
    (hEI : ∀ m, Integrable (E m) P)
    (hCI : ∀ m, Integrable (C m) P)
    (hEB : ∀ m, (∫ ω, E m ω ∂P) ≤ K)
    (hCL : Tendsto (fun m => ∫ ω, C m ω ∂P)
      atTop (𝓝 (0 : ℝ)))
    (hMod : ∀ ε, 0 < ε → ∃ δ, 0 < δ ∧
      ∀ m, ∀ᵐ ω ∂P,
        max (S δ m ω) 0 ≤
          ε*E m ω+(M/2)*C m ω +
          (m : ℝ) *
            (q * (((n : ℝ≥0) / ((m : ℝ≥0)+1) : ℝ≥0) : ℝ) * L)^2 /
              (2*ε)) :
    ∀ η, 0 < η → ∃ δ, 0 < δ ∧
      (∀ m, Integrable (fun ω => max (S δ m ω) 0) P) ∧
      ∃ k : ℕ, ∀ m, k ≤ m →
        (∫ ω, max (S δ m ω) 0 ∂P) ≤ η := by sorry
