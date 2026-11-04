-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p3_a_bvdrift_source_cofinal_mean_zero_random_clock_tsum
-- name    : AvramDividend.Classical.avram_p3_a_bvdrift_source_cofinal_mean_zero_random_clock_tsum
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-03T12:06:18.675577+00:00
-- url     : https://prove2.me/theorems/eb271e27-3b96-484c-a04f-2110d86a4f7a
-- title:
--   Original BV drift and actual negative-jump series at sample-dependent clock from source residual mean zero
-- statement:
--   For the original spectrally negative BV Levy process, the true physical drift minus the source's full negative left-jump magnitude series holds almost surely at any original sample-dependent time clock U. This is a direct pathwise transfer of Proved 5beba39a-1bdd-4512-a9a9-7adb5a30c233 and retains its explicit mean_zero assumptions. It does not introduce an alternative process, expected compensator or representation axiom.
-- source:
--   Exact source-a.e. all-time path theorem 5beba39a-1bdd-4512-a9a9-7adb5a30c233 specialised at t=U(ω), retaining original Ω/P/filtration/left-jump series.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_p3_a_bvdrift_original_cofinal_mean_zero_global_path

open MeasureTheory Filter Set Topology AvramDividend.Classical
open scoped NNReal ENNReal BigOperators

/-- Original BV drift-minus-real-jump series at an arbitrary sample-dependent
clock, inherited from the source all-horizon almost-sure event. -/

theorem AvramDividend.Classical.avram_p3_a_bvdrift_source_cofinal_mean_zero_random_clock_tsum
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
        else 0).toReal) ∂P) = 0)
    (U : Ω → ℝ≥0) :
    ∀ᵐ ω ∂P, X.X (U ω) ω = (U ω : ℝ) * X.drift -
        (∑' (v : ℝ≥0),
          if 0 < v ∧ v ≤ U ω then
            ENNReal.ofReal (Function.leftLim
              (fun z : ℝ≥0 => X.X z ω) v - X.X v ω)
          else 0).toReal := by sorry
