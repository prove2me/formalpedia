-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave5_04b_positive_cap_original_global_closed_stieltjes_budget
-- name    : AvramDividend.Classical.avram_wave5_04b_positive_cap_original_global_closed_stieltjes_budget
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-01T13:34:38.268616+00:00
-- url     : https://prove2.me/theorems/34cae2dd-10cd-475f-bd48-600f171bbf33
-- title:
--   Finite-or-infinite positive cap original-source complete discounted Stieltjes dividend horizon budget
-- statement:
--   For any positive ENNReal cap C (including ∞), an admissible source-specific strategy and the global cap-linear/infinite-w value extension, the actual discounted Stieltjes integral on [0,T] up to a pre-ruin horizon is bounded by V(x+X_T)-V(x+X_T-D_{T+}). All atoms including t=0, diffuse and singular-continuous components, and zero/cap contacts are controlled without strict interior occupation or a finite-cap assumption.
-- source:
--   The Proved complete discounted dividend Stieltjes horizon bound by right-limit total dividend mass plus Proved positive ENNReal-cap global value secant, admissible post-payment solvency and right-limit positivity.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave5_04b_positive_ennreal_cap_extension_global_secant
import Theorems.Thm_AvramDividend_Classical_avram_wave3_03_bv_discounted_closed_horizon_stieltjes_bound
import Theorems.Thm_AvramDividend_Classical_dividendStrategy_le_rightLimit

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

theorem AvramDividend.Classical.avram_wave5_04b_positive_cap_original_global_closed_stieltjes_budget
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (C : ℝ≥0∞) (hC : 0 < C)
    (q : ℝ) (hq : 0 ≤ q) (w V : ℝ → ℝ)
    (hw_cont : ContinuousOn w (Ici 0))
    (hw_smooth : ContDiffOn ℝ 1 w
      {z : ℝ | 0 < z ∧ ENNReal.ofReal z < C})
    (hw_grad : ∀ z : ℝ, 0 < z →
      ENNReal.ofReal z < C → 1 ≤ deriv w z)
    (hVtop : C = ⊤ → ∀ z : ℝ, V z = w z)
    (hVfinite : C ≠ ⊤ → ∀ z : ℝ,
      V z = if z ≤ C.toReal then w z
        else w C.toReal + (z - C.toReal))
    (D : ℝ≥0 → Ω → ℝ)
    (hD : IsAdmissibleLe X x C D)
    (ω : Ω) (T : ℝ≥0)
    (hPre : T = 0 ∨ (T : ℝ≥0∞) < ruinTime X x D ω) :
    (∫⁻ s in Icc (0 : ℝ) (T : ℝ),
      ENNReal.ofReal (Real.exp (-(q * s))) ∂(dividendMeasure D ω)) ≤
      ENNReal.ofReal
        (V (x + X.X T ω) -
          V (x + X.X T ω - rightLimit D T ω)) := by sorry
