-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p3_a_bvdrift_original_cofinal_laplace_global_intervals
-- name    : AvramDividend.Classical.avram_p3_a_bvdrift_original_cofinal_laplace_global_intervals
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-03T10:32:42.023032+00:00
-- url     : https://prove2.me/theorems/a2de9927-a506-4817-96cd-aa5582643123
-- title:
--   Cofinal-horizon source Laplace identities force global genuine BV drift-minus-jump intervals
-- statement:
--   For the same original BV spectrally negative Levy process, it suffices to know the exact actual-jump Laplace functional at a countable family T_n of source horizons such that every finite time lies beneath one T_n. One a.e. original-space event then yields all-time all-interval exact physical drift X.drift minus the actual intrinsic downward-jump mass. No Standing or independent model and no monotonicity of T_n are required.
-- source:
--   Specialise Proved 4677903e to each T n, intersect the countable full-measure events with ae_all_iff, and instantiate at an index dominating t via hT.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_p3_a_bvdrift_original_jump_laplace_only_exact_intervals

open MeasureTheory Filter Set Topology AvramDividend.Classical
open scoped NNReal ENNReal BigOperators

/-- Any countable cofinal family of original-jump Laplace identities provides
a single almost-sure BV drift-minus-actual-jumps formula at every interval. -/

theorem AvramDividend.Classical.avram_p3_a_bvdrift_original_cofinal_laplace_global_intervals
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hBV : X.BoundedVariation)
    (T : ℕ → ℝ≥0) (hT : ∀ t : ℝ≥0, ∃ n, t ≤ T n)
    (θ : ℝ) (hθ : 1 ≤ θ)
    (hLap : ∀ n : ℕ,
      (∫ ω : Ω, Real.exp (-(θ * (∑' (v : ℝ≥0),
          if 0 < v ∧ v ≤ T n then
            ENNReal.ofReal (Function.leftLim
              (fun z : ℝ≥0 => X.X z ω) v - X.X v ω)
          else 0).toReal)) ∂P) =
        Real.exp (-(T n : ℝ) *
          (∫ y in Iio (0 : ℝ), (1 - Real.exp (θ * y)) ∂X.ν))) :
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
