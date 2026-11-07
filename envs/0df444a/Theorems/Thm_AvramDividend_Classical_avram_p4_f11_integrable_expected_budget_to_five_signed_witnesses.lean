-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p4_f11_integrable_expected_budget_to_five_signed_witnesses
-- name    : AvramDividend.Classical.avram_p4_f11_integrable_expected_budget_to_five_signed_witnesses
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-06T23:16:50.995197+00:00
-- url     : https://prove2.me/theorems/8eac0e73-6bf5-4767-a99b-22817d2d6198
-- title:
--   Exact source-probability centring of an L1 expected budget into five signed witnesses
-- statement:
--   On the original SpectrallyNegativeLevy probability law, any integrable real payoff H with expected value at most a admits three integrable individually mean-zero compensator witnesses and two pointwise nonpositive signed remainders whose sum gives the payoff upper bound. Explicitly centre H by its expectation, put zero in two compensator slots and the expectation gap into one nonpositive remainder. The source physical expectation remains an independent, separately published lemma.
-- source:
--   Pure probability and real algebra in the original law; uses SpectrallyNegativeLevy.isProbability and pinned Mathlib integration. Reduces the five-witness object without hiding Ito/compensator assumptions.

import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_p4_f11_integrable_expected_budget_to_five_signed_witnesses
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (H : Ω → ℝ) (a : ℝ)
    (hHI : Integrable H P)
    (hBound : (∫ ω, H ω ∂P) ≤ a) :
    ∃ Mc Ms Ml G R : Ω → ℝ,
      Integrable Mc P ∧ Integrable Ms P ∧ Integrable Ml P ∧
      (∫ ω, Mc ω ∂P) = 0 ∧
      (∫ ω, Ms ω ∂P) = 0 ∧
      (∫ ω, Ml ω ∂P) = 0 ∧
      (∀ᵐ ω ∂P, G ω ≤ 0) ∧ (∀ᵐ ω ∂P, R ω ≤ 0) ∧
      (∀ᵐ ω ∂P,
        H ω ≤ a + Mc ω + Ms ω + Ml ω + G ω + R ω) := by sorry
