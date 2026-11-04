-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p3_a_bvdrift_original_cofinal_mean_zero_global_path
-- name    : AvramDividend.Classical.avram_p3_a_bvdrift_original_cofinal_mean_zero_global_path
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-03T10:37:24.711249+00:00
-- url     : https://prove2.me/theorems/5beba39a-1bdd-4512-a9a9-7adb5a30c233
-- title:
--   True BV Lévy global physical drift plus actual left jumps from cofinal mean-zero residuals
-- statement:
--   For the original BV spectrally negative Levy process, integrable mean-zero actual source physical residuals on a countable cofinal set of horizons imply a single almost-sure event on which X_t = t*X.drift minus the entire actual negative left-jump series for all t, with unchanged Ω,P,filtration and no Standing. The mean-zero source residuals remain an explicit genuine stochastic dependency.
-- source:
--   Proved cofinal mean-zero global intervals 31ea5690, actual source sum-to-intrinsic equality 3d5eead6 and source X.X_zero; use s=0 and simple rewrites.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_p3_a_bvdrift_original_cofinal_mean_zero_global_intervals
import Theorems.Thm_AvramDividend_Classical_avram_p3_a_bvdrift_original_jump_tsum_eq_intrinsic_measure

open MeasureTheory Filter Set Topology AvramDividend.Classical
open scoped NNReal ENNReal BigOperators

/-- Source BV pathwise drift-and-negative-jump identity at all times from
actual zero-mean residual conditions at arbitrary cofinal horizons. -/

theorem AvramDividend.Classical.avram_p3_a_bvdrift_original_cofinal_mean_zero_global_path
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hBV : X.BoundedVariation)
    (T : ℕ → ℝ≥0) (hT : ∀ t : ℝ≥0, ∃ n, t ≤ T n)
    (hInt : ∀ n : ℕ, Integrable (fun ω : Ω =>
      ((T n : ℝ) * X.drift - X.X (T n) ω) -
      (∑' (v : ℝ≥0),
        if 0 < v ∧ v ≤ T n then
          ENNReal.ofReal (Function.leftLim
            (fun z : ℝ≥0 => X.X z ω) v - X.X v ω)
        else 0).toReal) P)
    (hMean : ∀ n : ℕ, (∫ ω : Ω,
      (((T n : ℝ) * X.drift - X.X (T n) ω) -
      (∑' (v : ℝ≥0),
        if 0 < v ∧ v ≤ T n then
          ENNReal.ofReal (Function.leftLim
            (fun z : ℝ≥0 => X.X z ω) v - X.X v ω)
        else 0).toReal) ∂P) = 0) :
    ∀ᵐ ω ∂P, ∀ t : ℝ≥0,
      X.X t ω = (t : ℝ) * X.drift -
        (∑' (v : ℝ≥0),
          if 0 < v ∧ v ≤ t then
            ENNReal.ofReal (Function.leftLim
              (fun z : ℝ≥0 => X.X z ω) v - X.X v ω)
          else 0).toReal := by sorry
