-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p3_a_bvdrift_original_cofinal_mean_zero_global_intervals
-- name    : AvramDividend.Classical.avram_p3_a_bvdrift_original_cofinal_mean_zero_global_intervals
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-03T10:33:38.488184+00:00
-- url     : https://prove2.me/theorems/31ea5690-dc18-474b-bce3-5fb5abd27e50
-- title:
--   Cofinal original BV physical drift intervals from mean-zero actual source residuals
-- statement:
--   For the true original bounded variation Levy process, any countable cofinal sequence of deterministic horizons whose physical source jump deficit is integrable and has zero expectation suffices for a single a.e. event giving exact drift X.drift minus actual negative marked-jump mass on every interval. No Standing or auxiliary process, no monotonicity of the horizon sequence. The original mean-zero obligation remains explicit.
-- source:
--   Apply Proved ecc56f30 to each cofinal horizon, intersect all probability-one events via ae_all_iff, and choose an index with endpoint below that horizon.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_p3_a_bvdrift_any_BV_single_moment_exact_original_intervals

open MeasureTheory Filter Set Topology AvramDividend.Classical
open scoped NNReal ENNReal BigOperators

/-- Mean-zero actual BV residual on arbitrary cofinal horizons yields one
all-time full-measure set supporting the true original jump decomposition. -/

theorem AvramDividend.Classical.avram_p3_a_bvdrift_original_cofinal_mean_zero_global_intervals
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
    ∀ᵐ ω ∂P, ∀ s t : ℝ≥0, s ≤ t →
      X.X t ω - X.X s ω =
        ((t : ℝ) - (s : ℝ)) * X.drift -
        (∫⁻ p,
          (if s < p.1 ∧ p.1 ≤ t then ENNReal.ofReal (-p.2) else 0) ∂
          ((Measure.count.restrict {u : ℝ≥0 | 0 < u ∧
            X.X u ω - Function.leftLim
              (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
            (fun u : ℝ≥0 => (u,
              X.X u ω - Function.leftLim
                (fun v : ℝ≥0 => X.X v ω) u)))).toReal := by sorry
