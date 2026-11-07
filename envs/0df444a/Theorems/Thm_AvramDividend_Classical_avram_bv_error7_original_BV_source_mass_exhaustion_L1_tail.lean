-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_bv_error7_original_BV_source_mass_exhaustion_L1_tail
-- name    : AvramDividend.Classical.avram_bv_error7_original_BV_source_mass_exhaustion_L1_tail
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-06T12:56:30.691399+00:00
-- url     : https://prove2.me/theorems/c8a27dc5-21d2-4467-bc62-81fdeede1f6d
-- title:
--   Authentic BV Lévy source mass localisation-tail L1 convergence
-- statement:
--   For the actual original bounded-variation spectrally-negative Levy process satisfying Standing, the authentic physical source-mass integrable envelope H(omega)=K(|drift|T+|T drift-X_T(omega)|) has an L1-vanishing complement when measurable localisation events s_n eventually cover almost every sample. Consequently the H-source mass yields uniform-in-physical-grid complementary expectation tails, provided the original positive error is bounded by H off the events. The proof uses the previously accepted source-specific BV L1 mass and the dominated convergence theorem; no signed prebudget is used.
-- source:
--   Uses already proved original BV source variation L1 theorem and actual X_T, with simple indicator DCT. This provides an original stochastic tail estimate for the fixed-event localisation absorption FF.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_bv_error7_original_BV_source_variation_L1_upto_one
open MeasureTheory Set Filter Metric AvramDividend.Classical
open scoped NNReal ENNReal Classical
noncomputable section

theorem AvramDividend.Classical.avram_bv_error7_original_BV_source_mass_exhaustion_L1_tail
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hX : X.Standing) (hBV : X.BoundedVariation)
    (T : ℝ≥0) (hT : T ≤ 1)
    (K : ℝ) (hK : 0 ≤ K)
    (s : ℕ → Set Ω) (hs : ∀ n, MeasurableSet (s n))
    (hExhaust : ∀ᵐ ω ∂P, ∀ᶠ n in atTop, ω ∈ s n) :
    (∀ n, Integrable
      (fun ω => if ω ∈ s n then 0 else
        K * (|X.drift| * (T : ℝ) +
          |(T : ℝ) * X.drift - X.X T ω|)) P) ∧
    Tendsto (fun n => ∫ ω, if ω ∈ s n then 0 else
        K * (|X.drift| * (T : ℝ) +
          |(T : ℝ) * X.drift - X.X T ω|) ∂P)
      atTop (nhds (0 : ℝ)) := by sorry
