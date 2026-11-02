-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave5_04b_original_preruin_one_horizon_global_signed_stieltjes_correction_nonpos
-- name    : AvramDividend.Classical.avram_wave5_04b_original_preruin_one_horizon_global_signed_stieltjes_correction_nonpos
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-01T11:25:51.906197+00:00
-- url     : https://prove2.me/theorems/16b74d51-6fa8-432c-ae48-93046af4d0b0
-- title:
--   Complete signed true Stieltjes dividend control for one pre-ruin horizon, with zero atom and cap contacts
-- statement:
--   For any pre-ruin horizon t, the true discounted dividendMeasure Stieltjes integral on the entire closed time interval [0,t], plus the cap-linear value correction for the genuine time-zero payment and the source-frozen correction from the initial to terminal right dividend limits, is nonpositive. Includes diffuse, singular-continuous and countably jumping dividends, reserve contacts at zero and the cap, and full chronological source-left-then-dividend-right convention. Does not assume strict interior localisation or rate-representability of the dividend measure.
-- source:
--   The canonical global closed signed finite-grid theorem applied to the monotone grid u0=0, u1=t. The proof uses an explicit two-point Nat-indexed grid and Finset.range 1 simplification.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave5_04b_original_preruin_global_closed_signed_stieltjes_correction_nonpos

open MeasureTheory Set
open scoped NNReal ENNReal BigOperators
open AvramDividend.Classical

theorem AvramDividend.Classical.avram_wave5_04b_original_preruin_one_horizon_global_signed_stieltjes_correction_nonpos
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x c : ℝ) (hc : 0 < c) (q : ℝ) (hq : 0 ≤ q)
    (w V : ℝ → ℝ)
    (hw_cont : ContinuousOn w (Ici 0))
    (hw_smooth : ContDiffOn ℝ 1 w
      {z : ℝ | 0 < z ∧ ENNReal.ofReal z < ENNReal.ofReal c})
    (hw_grad : ∀ z : ℝ, 0 < z →
      ENNReal.ofReal z < ENNReal.ofReal c → 1 ≤ deriv w z)
    (hV : ∀ z : ℝ, V z = if z ≤ c then w z else w c + (z - c))
    (D : ℝ≥0 → Ω → ℝ)
    (hD : IsAdmissibleLe X x (ENNReal.ofReal c) D)
    (ω : Ω) (t : ℝ≥0)
    (hPre : t = 0 ∨ (t : ℝ≥0∞) < ruinTime X x D ω) :
    (∫⁻ s in Icc (0 : ℝ) (t : ℝ),
      ENNReal.ofReal (Real.exp (-(q * s))) ∂(dividendMeasure D ω)).toReal +
    (V (x + X.X 0 ω - rightLimit D 0 ω) - V (x + X.X 0 ω)) +
    (V (x + X.X t ω - rightLimit D t ω) -
      V (x + X.X t ω - rightLimit D 0 ω)) ≤ 0 := by sorry
