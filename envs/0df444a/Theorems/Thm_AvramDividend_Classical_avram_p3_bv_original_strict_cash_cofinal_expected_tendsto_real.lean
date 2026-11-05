-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p3_bv_original_strict_cash_cofinal_expected_tendsto_real
-- name    : AvramDividend.Classical.avram_p3_bv_original_strict_cash_cofinal_expected_tendsto_real
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-04T10:05:46.07926+00:00
-- url     : https://prove2.me/theorems/36f7b99a-87a5-408c-9d51-e2f35f2d2fb6
-- title:
--   Original stopped BV strict dividend cash expectations converge along every nonnegative cofinal grid
-- statement:
--   For the actual original spectrally negative Levy process, actual admissible dividend control and its stopped Stieltjes payment measure, real discounted strict-horizon cash converges in expectation along any increasing cofinal nonnegative clock sequence. The accepted exact pathwise cofinal theorem and strict cash L1 bound give genuine domination, while the at-horizon right-payment atom remains excluded.
-- source:
--   Accepted f8dca0da original pathwise cofinal cash convergence; 67a9c5bf original strict stopped cash L1; e1100117 original strict horizon monotonicity; 512282cc original right-limit domination; pinned Mathlib MeasureTheory.tendsto_integral_filter_of_dominated_convergence.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_p3_bv_original_cash_strict_horizon_mono
import Theorems.Thm_AvramDividend_Classical_avram_p3_bv_original_strict_cash_rightlimit_bound
import Theorems.Thm_AvramDividend_Classical_avram_p3_bv_original_strict_cash_L1
import Theorems.Thm_AvramDividend_Classical_avram_p3_bv_original_strict_cash_cofinal_tendsto_real
open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_p3_bv_original_strict_cash_cofinal_expected_tendsto_real
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (x : ℝ) (C : ℝ≥0∞)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (q : ℝ) (hq : 0 ≤ q) (S : ℝ≥0)
    (u : ℕ → ℝ) (hmono : Monotone u)
    (hu : ∀ n, 0 ≤ u n)
    (hbelow : ∀ n, u n ≤ (S : ℝ))
    (hcover : ∀ s : ℝ, s < (S : ℝ) → ∃ n, s < u n) :
    Tendsto (fun n => ∫ ω : Ω,
      (∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Iio (u n),
        ENNReal.ofReal (Real.exp (-(q * t))) ∂dividendMeasure D ω).toReal ∂P)
      atTop (nhds (∫ ω : Ω,
        (∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Iio (S : ℝ),
          ENNReal.ofReal (Real.exp (-(q * t))) ∂dividendMeasure D ω).toReal ∂P)) := by sorry
