-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_ubv_loc6_original_masked_reward_dominates_exact_F
-- name    : AvramDividend.Classical.avram_ubv_loc6_original_masked_reward_dominates_exact_F
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-06T23:40:35.636645+00:00
-- url     : https://prove2.me/theorems/ef1ac2df-d99f-4812-823a-5578e79d7e3c
-- title:
--   Exact original stopped reward lies below zero-clock-masked reward at every physical stopping time
-- statement:
--   For the actual original right-limit stopped reserve and closed Iic dividend cash F k, prove F k ω ≤ (if σ k ω=0 then w x else F k ω), uniformly in every compact clock. At zero it uses the genuine HJB initial jump secant and full time-zero cash atom; at positive times it is equality. This is the source-exact bridge from signed Ito mask inequalities to unmasked Fatou reward budget.
-- source:
--   Specialise Proved zero-clock original physical payoff theorem 581f5b9e, with the exact same sigma k and F k, then split on the zero clock; no integrability, convergence, martingale or expected-value hypotheses.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy

open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_ubv_loc6_original_masked_reward_dominates_exact_F
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x q : ℝ) (w : ℝ → ℝ) (C : ℝ≥0∞)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (hjump : ∀ ω (t : ℝ≥0),
      (t = 0 ∨ (t : ℝ≥0∞) < ruinTime X x D ω) →
      rightLimit D t ω - D t ω ≤
        w (riskProcess X x D t ω) -
          w (riskProcess X x D t ω -
            (rightLimit D t ω - D t ω)))
    (σ : ℕ → Ω → ℝ≥0) (F : ℕ → Ω → ℝ)
    (hFsource : ∀ k ω, F k ω =
      Real.exp (-(q * (σ k ω : ℝ))) *
        w (if σ k ω = 0 ∨
              (σ k ω : ℝ≥0∞) < ruinTime X x D ω then
            x + X.X (σ k ω) ω - rightLimit D (σ k ω) ω
          else riskProcess X x D (σ k ω) ω) +
      (∫⁻ s in paymentTimes (ruinTime X x D ω) ∩ Iic (σ k ω : ℝ),
        ENNReal.ofReal (Real.exp (-(q * s)))
        ∂(dividendMeasure D ω)).toReal)
    (k : ℕ) (ω : Ω) :
    F k ω ≤ (if σ k ω = 0 then w x else F k ω) := by sorry
