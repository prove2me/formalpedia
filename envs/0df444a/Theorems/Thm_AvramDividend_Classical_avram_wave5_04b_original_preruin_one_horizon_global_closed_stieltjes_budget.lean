-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave5_04b_original_preruin_one_horizon_global_closed_stieltjes_budget
-- name    : AvramDividend.Classical.avram_wave5_04b_original_preruin_one_horizon_global_closed_stieltjes_budget
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-01T11:13:29.24802+00:00
-- url     : https://prove2.me/theorems/c2dbf794-c5de-47c2-8730-60e58ddab67d
-- title:
--   One-horizon original-source genuine discounted Stieltjes dividend budget, boundary-safe and including time zero
-- statement:
--   For any horizon t strictly before ruin (or t=0), the actual discounted dividendMeasure Stieltjes lower integral over [0,t] is bounded by the cap-linear potential drop from the genuine time-zero payment and the source-frozen value drop from the previous to current dividend right limits at t. The full measure includes singular-continuous, diffuse and countably atomic dividends, with no strict-interior reserve assumption and no derivative evaluated at a boundary.
-- source:
--   Proved global closed-horizon exact source budget ed9de935-bfdb-4622-806d-2bf785db782e specialised to the monotone grid u0=0,u1=t.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave5_04b_original_preruin_global_closed_discounted_stieltjes_grid_budget

open MeasureTheory Set
open scoped NNReal ENNReal BigOperators
open AvramDividend.Classical

theorem AvramDividend.Classical.avram_wave5_04b_original_preruin_one_horizon_global_closed_stieltjes_budget
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x c : ℝ) (hc : 0 < c) (q : ℝ) (hq : 0 ≤ q) (w : ℝ → ℝ)
    (hw_cont : ContinuousOn w (Ici 0))
    (hw_smooth : ContDiffOn ℝ 1 w
      {z : ℝ | 0 < z ∧ ENNReal.ofReal z < ENNReal.ofReal c})
    (hw_grad : ∀ z : ℝ, 0 < z →
      ENNReal.ofReal z < ENNReal.ofReal c → 1 ≤ deriv w z)
    (D : ℝ≥0 → Ω → ℝ)
    (hD : IsAdmissibleLe X x (ENNReal.ofReal c) D)
    (ω : Ω) (t : ℝ≥0)
    (hPre : t = 0 ∨ (t : ℝ≥0∞) < ruinTime X x D ω) :
    (∫⁻ s in Icc (0 : ℝ) (t : ℝ),
      ENNReal.ofReal (Real.exp (-(q * s))) ∂(dividendMeasure D ω)) ≤
    ENNReal.ofReal (
      (if x + X.X 0 ω ≤ c then w (x + X.X 0 ω)
        else w c + (x + X.X 0 ω - c)) -
      (if x + X.X 0 ω - rightLimit D 0 ω ≤ c
        then w (x + X.X 0 ω - rightLimit D 0 ω)
        else w c + ((x + X.X 0 ω - rightLimit D 0 ω) - c))) +
    ENNReal.ofReal (
        (if x + X.X t ω - rightLimit D 0 ω ≤ c
          then w (x + X.X t ω - rightLimit D 0 ω)
          else w c + (x + X.X t ω - rightLimit D 0 ω - c)) -
        (if x + X.X t ω - rightLimit D t ω ≤ c
          then w (x + X.X t ω - rightLimit D t ω)
          else w c + (x + X.X t ω - rightLimit D t ω - c))) := by sorry
