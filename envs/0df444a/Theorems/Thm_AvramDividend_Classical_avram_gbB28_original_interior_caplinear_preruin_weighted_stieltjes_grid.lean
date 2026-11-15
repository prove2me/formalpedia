-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_gbB28_original_interior_caplinear_preruin_weighted_stieltjes_grid
-- name    : AvramDividend.Classical.avram_gbB28_original_interior_caplinear_preruin_weighted_stieltjes_grid
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-14T13:12:26.234215+00:00
-- url     : https://prove2.me/theorems/38383927-e073-44c0-8140-e466d4cecdf1
-- title:
--   Original pre-ruin weighted Stieltjes mesh inequality at independent interior clipping cap
-- statement:
--   For any monotone original physical mesh strictly before ruin and any nonnegative cell weights, the weighted sum of signed discounted dividend measure and cap-linear postpayment correction is nonpositive. The clipping cap c can be below the dividend strategy actual admissible cap C.
-- source:
--   Summing the Proved B25 original pre-ruin signed Stieltjes cell inequality with nonnegative weights. This provides the finite-grid dividend component for the Gaussian cash ledger while preserving original X,D,rightLimit D.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_gbB25_original_preruin_interior_caplinear_stieltjes_signed_control
open MeasureTheory Set Finset AvramDividend.Classical
open scoped NNReal ENNReal BigOperators
noncomputable section

theorem AvramDividend.Classical.avram_gbB28_original_interior_caplinear_preruin_weighted_stieltjes_grid
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x c : ℝ) (hc : 0 < c) (C : ℝ≥0∞) (q : ℝ) (hq : 0 ≤ q)
    (w V : ℝ → ℝ)
    (hw_cont : ContinuousOn w (Ici 0))
    (hw_smooth : ContDiffOn ℝ 1 w
      {z : ℝ | 0 < z ∧ ENNReal.ofReal z < ENNReal.ofReal c})
    (hw_grad : ∀ z : ℝ, 0 < z →
      ENNReal.ofReal z < ENNReal.ofReal c → 1 ≤ deriv w z)
    (hV : ∀ z : ℝ, V z = if z ≤ c then w z else w c + (z - c))
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (ω : Ω) (u : ℕ → ℝ≥0) (N : ℕ)
    (hgrid : ∀ i : ℕ, i < N → u i ≤ u (i + 1))
    (hpre : ∀ i : ℕ, i < N →
      u (i + 1) = 0 ∨ (u (i + 1) : ℝ≥0∞) < ruinTime X x D ω)
    (r : ℕ → ℝ) (hr : ∀ i : ℕ, i < N → 0 ≤ r i) :
    (∑ i ∈ Finset.range N, r i *
      ((∫⁻ t in Ioc (u i : ℝ) (u (i + 1) : ℝ),
          ENNReal.ofReal (Real.exp (-(q * t)))
          ∂(dividendMeasure D ω)).toReal +
        V (x + X.X (u (i + 1)) ω - rightLimit D (u (i + 1)) ω) -
        V (x + X.X (u (i + 1)) ω - rightLimit D (u i) ω))) ≤ 0 := by sorry
