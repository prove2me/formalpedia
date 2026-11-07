-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_bv_jump8_source_cutoff_laplace_future_stationary
-- name    : AvramDividend.Classical.avram_bv_jump8_source_cutoff_laplace_future_stationary
-- status  : Open
-- author  : @WillR
-- created : 2026-11-06T17:30:36.503062+00:00
-- url     : https://prove2.me/theorems/b64275e2-302f-43a1-921b-fee8f79ee4ed
-- title:
--   Original marked cutoff exponential future one-cell expectation is stationary
-- statement:
--   For the actual spectrally negative Lévy path satisfying Standing, the expected cutoff-weighted exponential of the intrinsic marks in the strict-left, closed-right future cell (n,n+1] equals that in (0,1]. Requires transferring stationary increments of the original process to its own marked jumps.
-- source:
--   Source exact mission original intrinsic marked random measure. Disjoint window identity and stochastic conditions separated. Closures are combined by Lean integral_congr_ae and two expectation identities. The BV magnitude bound is already Proved 8fdf098e.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open MeasureTheory Set Filter
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_bv_jump8_source_cutoff_laplace_future_stationary
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (hBV : X.BoundedVariation) :
    ∀ (n k : ℕ),
      (∫ ω : Ω, Real.exp (-((∫⁻ p : ℝ≥0 × ℝ,
        if (n : ℝ≥0) < p.1 ∧ p.1 ≤ ((n + 1) : ℝ≥0) ∧
            p.2 < -(1 / ((k : ℝ) + 1)) then ENNReal.ofReal (-p.2) else 0 ∂
        ((Measure.count.restrict {u : ℝ≥0 |
          0 < u ∧ X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u, X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))).toReal)) ∂P) =
      (∫ ω : Ω, Real.exp (-((∫⁻ p : ℝ≥0 × ℝ,
        if 0 < p.1 ∧ p.1 ≤ (1 : ℝ≥0) ∧
            p.2 < -(1 / ((k : ℝ) + 1)) then ENNReal.ofReal (-p.2) else 0 ∂
        ((Measure.count.restrict {u : ℝ≥0 |
          0 < u ∧ X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u, X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))).toReal)) ∂P) := by sorry
