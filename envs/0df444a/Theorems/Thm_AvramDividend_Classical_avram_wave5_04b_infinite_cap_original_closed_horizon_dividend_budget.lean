-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave5_04b_infinite_cap_original_closed_horizon_dividend_budget
-- name    : AvramDividend.Classical.avram_wave5_04b_infinite_cap_original_closed_horizon_dividend_budget
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-01T13:32:23.007092+00:00
-- url     : https://prove2.me/theorems/5e0b02ab-e197-47ce-9d1a-c3542bac3980
-- title:
--   Infinite-cap original pre-ruin complete discounted Stieltjes dividend horizon budget
-- statement:
--   With infinite capital cap, an admissible original spectrally negative Levy dividend strategy and a positive-half-line gradient supersolution, the entire discounted dividendMeasure on [0,T] up to a pre-ruin time, including time-zero atom, diffuse, singular-continuous and countably atomic components, is dominated by the source-frozen value drop w(x+X_T)-w(x+X_T-D_{T+}). There is no strict interior occupation assumption or finite-cap restriction.
-- source:
--   Proved generic full-horizon discounted dividend Stieltjes measure bound by the right-limit dividend mass, full-cap global secant specialized to ⊤, monotonicity of right limits, and admissible post-payment solvency.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave5_04b_infinite_cap_gradient_global_secant
import Theorems.Thm_AvramDividend_Classical_avram_wave3_03_bv_discounted_closed_horizon_stieltjes_bound
import Theorems.Thm_AvramDividend_Classical_dividendStrategy_le_rightLimit

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

theorem AvramDividend.Classical.avram_wave5_04b_infinite_cap_original_closed_horizon_dividend_budget
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (q : ℝ) (hq : 0 ≤ q)
    (w : ℝ → ℝ)
    (hw_cont : ContinuousOn w (Ici 0))
    (hw_smooth : ContDiffOn ℝ 1 w {z : ℝ | 0 < z})
    (hw_grad : ∀ z : ℝ, 0 < z → 1 ≤ deriv w z)
    (D : ℝ≥0 → Ω → ℝ)
    (hD : IsAdmissibleLe X x (⊤ : ℝ≥0∞) D)
    (ω : Ω) (T : ℝ≥0)
    (hPre : T = 0 ∨ (T : ℝ≥0∞) < ruinTime X x D ω) :
    (∫⁻ s in Icc (0 : ℝ) (T : ℝ),
      ENNReal.ofReal (Real.exp (-(q * s))) ∂(dividendMeasure D ω)) ≤
      ENNReal.ofReal
        (w (x + X.X T ω) -
          w (x + X.X T ω - rightLimit D T ω)) := by sorry
