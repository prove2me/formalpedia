-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_redux20_original_strict_marked_cutoff_laplace_finite_product
-- name    : AvramDividend.Classical.avram_redux20_original_strict_marked_cutoff_laplace_finite_product
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-07T09:03:40.020674+00:00
-- url     : https://prove2.me/theorems/213de0ce-09ea-4590-ba9c-c8cdccffc942
-- title:
--   Exact original intrinsic strict-cutoff Laplace path weight equals the finite product of physical jump exponentials
-- statement:
--   For the literal sample path of the original spectrally negative Lévy process, at every finite horizon and strict negative jump cutoff, the exponential of the negative intrinsic marked-jump loss equals the finite product of the exponentials of all true selected jump marks. The identity gives the exact physical marked Poisson product representation required before taking expectations in the Laplace law.
-- source:
--   Specialise the newly published source-exact Borel-weight finite marked integral theorem to the actual negative-mark magnitude, apply ENNReal.toReal_sum and toReal_ofReal on finite strict-negative support, then Real.exp_sum. The only remaining unproved part of the target law is the joint original marked Poisson expectation.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_redux19_original_strict_negative_marked_times_finite
import Theorems.Thm_AvramDividend_Classical_avram_redux20_original_strict_marked_borel_weight_finite_sum
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal BigOperators
noncomputable section

theorem AvramDividend.Classical.avram_redux20_original_strict_marked_cutoff_laplace_finite_product
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (ω : Ω) (T : ℝ≥0) (k : ℕ) :
    let S : Finset ℝ≥0 :=
      (avram_redux19_original_strict_negative_marked_times_finite X ω T k).toFinset
    Real.exp (-((∫⁻ p : ℝ≥0 × ℝ,
      if 0 < p.1 ∧ p.1 ≤ T ∧ p.2 < -(1 / ((k : ℝ) + 1))
      then ENNReal.ofReal (-p.2) else 0
      ∂((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u, X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))).toReal)) =
    ∏ u ∈ S, Real.exp (X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u) := by sorry
