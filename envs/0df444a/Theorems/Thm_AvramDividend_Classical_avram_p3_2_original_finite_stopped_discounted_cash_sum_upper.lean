-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p3_2_original_finite_stopped_discounted_cash_sum_upper
-- name    : AvramDividend.Classical.avram_p3_2_original_finite_stopped_discounted_cash_sum_upper
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-05T23:31:33.038993+00:00
-- url     : https://prove2.me/theorems/30190623-9ef2-4064-aa6a-99e4ebdfb8a4
-- title:
--   Finite original once-discounted cash is bounded by left-weighted physical stopped mass
-- statement:
--   The original strictly stopped physical Stieltjes cash integral on a finite collection of mesh cells, plus the zero-time atom, is at most the corresponding finite sum of unweighted cash masses discounted at each left endpoint plus the unchanged zero-time atom.
-- source:
--   Finset.sum_le_sum of the fully Proved exact original left-endpoint cash bound, with add_le_add_left retaining the time-zero atom.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_p3_2_original_exact_discounted_cash_cell_upper

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_p3_2_original_finite_stopped_discounted_cash_sum_upper
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ) (ω : Ω)
    (q : ℝ) (hq : 0 ≤ q) (T : ℝ≥0) (m n : ℕ) :
    let τ : ℝ≥0 :=
      (min (ruinTime X x D ω) (T : ℝ≥0∞)).toNNReal
    let u : ℕ → ℝ≥0 := fun j =>
      min (((min j (m + 1) : ℕ) : ℝ≥0) *
        (T / (m + 1))) τ
    ENNReal.ofReal (rightLimit D 0 ω) +
      (∑ i ∈ Finset.range n,
        (∫⁻ t in paymentTimes (ruinTime X x D ω) ∩
            Ioc (u i : ℝ) (u (i + 1) : ℝ),
          ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω))) ≤
      ENNReal.ofReal (rightLimit D 0 ω) +
      (∑ i ∈ Finset.range n,
        ENNReal.ofReal (Real.exp (-(q * (u i : ℝ)))) *
          (∫⁻ t in paymentTimes (ruinTime X x D ω) ∩
              Ioc (u i : ℝ) (u (i + 1) : ℝ),
            (1 : ℝ≥0∞) ∂(dividendMeasure D ω))):= by sorry
