-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p3_a_bvdrift_source_single_mean_zero_bounded_random_clocks
-- name    : AvramDividend.Classical.avram_p3_a_bvdrift_source_single_mean_zero_bounded_random_clocks
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-03T12:09:46.556463+00:00
-- url     : https://prove2.me/theorems/b584687e-e048-42ac-980d-b0d1bad64762
-- title:
--   Original BV exact negative-jump source clock budget from a single finite-horizon mean_zero condition
-- statement:
--   For the same original bounded-variation spectrally negative Levy process, assume only the exact source mean_zero finite-horizon residual identity at T. For any original sample-dependent clocks S≤U≤T almost everywhere, the true original path increment equals physical drift times clock increment minus the genuine intrinsic marked negative-jump mass on (S,U]. The statement needs no cofinal family, no standing assumption and no alternative process.
-- source:
--   Direct specialisation of remotely Proved finite-horizon source all-interval theorem ecc56f30-3613-4ab5-a796-bac54e9afa36 to S(ω), U(ω), using the a.e. ordering and upper-bound clock events.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_p3_a_bvdrift_any_BV_single_moment_exact_original_intervals

open MeasureTheory Filter Set Topology AvramDividend.Classical
open scoped NNReal ENNReal BigOperators

/-- One finite-horizon actual-source BV Laplace or residual moment condition
transfers the full marked negative-jump budget to ordered random clocks. -/

theorem AvramDividend.Classical.avram_p3_a_bvdrift_source_single_mean_zero_bounded_random_clocks
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hBV : X.BoundedVariation)
    (T : ℝ≥0)
    (hIntegrable : Integrable (fun ω : Ω =>
      ((T : ℝ) * X.drift - X.X T ω) -
        (∑' (v : ℝ≥0),
          if 0 < v ∧ v ≤ T then
            ENNReal.ofReal (Function.leftLim
              (fun z : ℝ≥0 => X.X z ω) v - X.X v ω)
          else 0).toReal) P)
    (hMeanZero : (∫ ω : Ω,
      (((T : ℝ) * X.drift - X.X T ω) -
        (∑' (v : ℝ≥0),
          if 0 < v ∧ v ≤ T then
            ENNReal.ofReal (Function.leftLim
              (fun z : ℝ≥0 => X.X z ω) v - X.X v ω)
          else 0).toReal) ∂P) = 0)
    (S U : Ω → ℝ≥0)
    (hSU : ∀ᵐ ω ∂P, S ω ≤ U ω)
    (hUT : ∀ᵐ ω ∂P, U ω ≤ T) :
    ∀ᵐ ω ∂P, X.X (U ω) ω - X.X (S ω) ω =
        ((U ω : ℝ) - (S ω : ℝ)) * X.drift -
        (∫⁻ p,
          (if S ω < p.1 ∧ p.1 ≤ U ω then ENNReal.ofReal (-p.2) else 0) ∂
          ((Measure.count.restrict {u : ℝ≥0 | 0 < u ∧
            X.X u ω - Function.leftLim
              (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
            (fun u : ℝ≥0 => (u,
              X.X u ω - Function.leftLim
                (fun v : ℝ≥0 => X.X v ω) u)))).toReal := by sorry
