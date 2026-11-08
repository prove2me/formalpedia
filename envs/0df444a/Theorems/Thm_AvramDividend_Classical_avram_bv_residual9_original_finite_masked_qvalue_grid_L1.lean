-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_bv_residual9_original_finite_masked_qvalue_grid_L1
-- name    : AvramDividend.Classical.avram_bv_residual9_original_finite_masked_qvalue_grid_L1
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-07T15:01:28.06506+00:00
-- url     : https://prove2.me/theorems/1b5b80ca-d76d-4520-9525-1204a882f739
-- title:
--   The literal original stopped physical-grid discounted q times pre-jump value sum is L1
-- statement:
--   For every fixed physical grid whose finitely many left-endpoint times are no later than T, the original finite stopped HJB sum contribution from -q*w(Z_i), retaining the strict pre-ruin and cap-interior mask and actual time widths, is integrable. This is a finite-sum consequence of Proved d6232304, independent of generator and raw R L1. The bounded time-grid hypothesis is satisfied by the original uniform grid.
-- source:
--   AVRAM BV-RESIDUAL9 exact original finite stopped-grid q*w component of edb6442e.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
open Classical MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_bv_residual9_original_finite_masked_qvalue_grid_L1
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hBV : X.BoundedVariation)
    (q : ℝ) (w : ℝ → ℝ)
    (hw_cont : ContinuousOn w (Ici 0))
    (hw_neg : ∀ y < 0, w y = 0)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D)
    (T : ℝ≥0) (C : ℝ≥0∞)
    (u : ℕ → ℕ → ℝ≥0) (n : ℕ)
    (hu : ∀ i ∈ Finset.range (n + 1), u n i ≤ T) :
    Integrable (fun ω =>
      ∑ i ∈ Finset.range (n + 1),
        (let Z : ℝ := Function.leftLim
          (fun s : ℝ≥0 => x + X.X s ω - rightLimit D s ω) (u n i)
         if (u n i : ℝ≥0∞) < ruinTime X x D ω ∧
             0 < Z ∧ ENNReal.ofReal Z < C then
           Real.exp (-(q * (u n i : ℝ))) * (q * w Z)
         else 0) *
        ((u n (i + 1) : ℝ) - (u n i : ℝ))) P := by sorry
