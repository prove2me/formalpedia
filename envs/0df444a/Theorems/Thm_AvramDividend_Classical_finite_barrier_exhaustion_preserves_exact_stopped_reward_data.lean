-- Prove2me | Theorems.Thm_AvramDividend_Classical_finite_barrier_exhaustion_preserves_exact_stopped_reward_data
-- name    : AvramDividend.Classical.finite_barrier_exhaustion_preserves_exact_stopped_reward_data
-- status  : Proved
-- author  : @scuba8684
-- created : 2026-11-26T07:39:44.604986+00:00
-- url     : https://prove2.me/theorems/9ca737c5-e97e-50cd-8455-da9481e84293
-- title:
--   Finite barriers eventually preserve exact ruin-clipped dividend reward data
-- statement:
--   Fix an admissible left-continuous dividend strategy for a spectrally negative Lévy surplus and a finite integer horizon. For the increasing caps $x+k+1$, construct admissible finite-cap strategies on the same probability space whose exact stopped data agree eventually on each path with the original strategy.
--
--   The data are the ruin-clipped clock, its terminal reserve with the postpayment convention under survival (and at time zero), and the original Stieltjes measure restricted to payments before ruin and through the clock. Agreement of the measures preserves every discounted cash integral, including the time-zero and surviving horizon atoms. This provides the finite-to-uncapped passage for exact stopped rewards without a generator or candidate assumption.
-- source:
--   Avram, Palmowski and Pistorius (2007), Sections 2 and 3.3, https://arxiv.org/pdf/math/0702893#page=8 (strategy and fixed barrier definitions); Proposition 4(i), https://arxiv.org/pdf/math/0702893#page=19 (finite and infinite caps).

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy

open Filter MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal

theorem AvramDividend.Classical.finite_barrier_exhaustion_preserves_exact_stopped_reward_data
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (x : ℝ) (hx : 0 ≤ x)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissible X x D) (n : ℕ) :
  let cap : ℕ → ℝ := fun k => x + (k : ℝ) + 1
  let clock : (ℝ≥0 → Ω → ℝ) → Ω → ℝ≥0 := fun L ω =>
    (min (ruinTime X x L ω) (n : ℝ≥0∞)).toNNReal
  let terminal : (ℝ≥0 → Ω → ℝ) → Ω → ℝ := fun L ω =>
    if clock L ω = 0 ∨ (clock L ω : ℝ≥0∞) < ruinTime X x L ω
    then x + X.X (clock L ω) ω - rightLimit L (clock L ω) ω
    else riskProcess X x L (clock L ω) ω
  let cashMeasure : (ℝ≥0 → Ω → ℝ) → Ω → Measure ℝ := fun L ω =>
    (dividendMeasure L ω).restrict
      (paymentTimes (ruinTime X x L ω) ∩ Iic (clock L ω : ℝ))
  ∃ E : ℕ → (ℝ≥0 → Ω → ℝ),
    (∀ k, IsAdmissibleLe X x (ENNReal.ofReal (cap k)) (E k)) ∧
    ∀ ω, ∀ᶠ k : ℕ in atTop,
      clock (E k) ω = clock D ω ∧
        terminal (E k) ω = terminal D ω ∧
        cashMeasure (E k) ω = cashMeasure D ω := by sorry
