-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_b241_original_ruinclipped_allcap_physical_cash_left_to_right_discount_mesh_correction
-- name    : AvramDividend.Classical.avram_b241_original_ruinclipped_allcap_physical_cash_left_to_right_discount_mesh_correction
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-14T21:22:28.193463+00:00
-- url     : https://prove2.me/theorems/140be463-6090-46de-917c-fcaf7dcfc2cf
-- title:
--   Original ruin-clipped all-cap physical Stieltjes cash source cell bound with exact left-to-right discount mesh correction
-- statement:
--   For any actual original pre-ruin dividend cell (a,b], preserve the true discounted full Stieltjes cash and original source frozen right-dividend potential Z versus actual postpayment Y. The full cash plus right-endpoint-discounted postpayment correction is bounded by the exact discount decrement (exp(-qa)-exp(-qb)) times the original caplinear payoff decrease V(Z)-V(Y). This is precisely the correction needed to combine the B238 true stopped source spatial telescope, which discounts right-endpoint payments, with the B240 cash control, which uses left-endpoint discount. It accounts for original time-zero/right payments and prevents falsely treating within-cell discount as constant.
-- source:
--   Rewrite Proved B240 original allcap frozen-source signed full Stieltjes inequality using the scalar exact identity e(b)·(V(Y)-V(Z)) - (e(a)-e(b))·(V(Z)-V(Y)) = e(a)·(V(Y)-V(Z)).

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_b240_original_ruinclipped_mixed_allcap_discounted_full_stieltjes_source_sign
open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_b241_original_ruinclipped_allcap_physical_cash_left_to_right_discount_mesh_correction
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x q : ℝ) (hq : 0 ≤ q)
    (C : ℝ≥0∞) (hC : 0 < C) (w : ℝ → ℝ)
    (hw_cont : ContinuousOn w (Ici 0))
    (hw_smooth : ContDiffOn ℝ 1 w
      {z : ℝ | 0 < z ∧ ENNReal.ofReal z < C})
    (hw_grad : ∀ z : ℝ, 0 < z →
      ENNReal.ofReal z < C → 1 ≤ deriv w z)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (ω : Ω) (a b : ℝ≥0) (hab : a ≤ b)
    (hPre : b = 0 ∨
      (b : ℝ≥0∞) < ruinTime X x D ω) :
    let V : ℝ → ℝ := fun z =>
      if C = ⊤ then w z else
      if z ≤ C.toReal then w z else w C.toReal + (z - C.toReal)
    let Y : ℝ := x + X.X b ω - rightLimit D b ω
    let Z : ℝ := x + X.X b ω - rightLimit D a ω
    (∫⁻ t in Ioc (a : ℝ) (b : ℝ),
      ENNReal.ofReal (Real.exp (-(q * t)))
      ∂(dividendMeasure D ω)).toReal +
      Real.exp (-(q * (b : ℝ))) * (V Y - V Z) ≤
      (Real.exp (-(q * (a : ℝ))) -
       Real.exp (-(q * (b : ℝ)))) * (V Z - V Y) := by sorry
