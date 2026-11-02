-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave7_ubv_original_nonmonotone_countable_horizon_exact_discounted_integral_domains
-- name    : AvramDividend.Classical.avram_wave7_ubv_original_nonmonotone_countable_horizon_exact_discounted_integral_domains
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-01T19:58:28.550844+00:00
-- url     : https://prove2.me/theorems/1ac18910-2e0a-446b-b39d-ac44d7b9a75c
-- title:
--   Original UBV common a.s. eventual exact discounted dividend integral domains at all countable horizons
-- statement:
--   For the actual original Levy source X and admissible D and an arbitrary nonmonotone extended random-clock family S_n with liminf S_n=top almost surely, there is one original probability-one event on which, for each finite nonnegative horizon in a prescribed countable family, all sufficiently late original clipped-clock full dividendMeasure D integrals agree exactly with the ruin-time truncated discounted dividend integral. The eventual threshold may depend on path and horizon. This is equality of already-defined domains only, not an integration formula or budget theorem.
-- source:
--   Accepted original countable-horizon payment domain stabilisation theorem 4fd8c76e-b059-4033-88fd-af9cbda41f92.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave7_ubv_original_nonmonotone_all_countable_horizons_payment_domain_stabilises

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_wave7_ubv_original_nonmonotone_countable_horizon_exact_discounted_integral_domains
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hBV : ¬ X.BoundedVariation)
    (x : ℝ) (C : ℝ≥0∞)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (q : ℝ) (S : ℕ → Ω → ℝ≥0∞)
    (hSliminfAE : ∀ᵐ ω ∂P,
      (⨆ n : ℕ, ⨅ k : ℕ, S (n + k) ω) = ⊤)
    (horizons : ℕ → ℝ)
    (hT : ∀ k : ℕ, 0 ≤ horizons k) :
    ∀ᵐ ω ∂P, ∀ k : ℕ, ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
      (∫⁻ t in paymentTimes
          (min (ruinTime X x D ω) (S n ω)) ∩ Iic (horizons k),
        ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω)) =
      (∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Iic (horizons k),
        ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω)) := by sorry
