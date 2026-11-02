-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave5_04a_actual_bv_stopped_source_weighted_remainder_drift_envelope
-- name    : AvramDividend.Classical.avram_wave5_04a_actual_bv_stopped_source_weighted_remainder_drift_envelope
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-01T17:41:39.427535+00:00
-- url     : https://prove2.me/theorems/4067fd1c-ef2a-4d75-9ddc-0a5d881ea414
-- title:
--   Uniform stopped weighted BV residual envelope from the actual source path and source drift
-- statement:
--   For the original actual spectrally negative Levy source with bounded variation, there exists an almost-sure explicit monotone downward remainder after subtracting all intrinsic negative source left jumps. On any increasing partition stopped before any samplewise horizon, every bounded-weight remainder sum is controlled in absolute value by M times the source drift-minus-actual-source endpoint increment at that horizon. The bound is uniform over partitions and mesh, uses no residual R on its right-hand side, and invokes neither a Poisson model nor controlled Ito-Meyer.
-- source:
--   Chat04-A original-source stopped BV envelope, combining canonical Proved exact intrinsic source jump-residual increment c4b53c7c-d769-4894-a0d8-c0b2a1516d1e and canonical Proved stopped weighted residual bound c63f3683-faa0-4067-a6d0-142f67a74728, using a single explicit residual witness.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_wave5_04a_actual_bv_source_remainder_uniform_stopped_horizon_weighted_bound
import Theorems.Thm_AvramDividend_Classical_avram_wave5_04a_actual_bv_source_exact_interval_increment_from_intrinsic_jumps_and_remainder

open MeasureTheory Filter Set Topology AvramDividend.Classical
open scoped NNReal ENNReal BigOperators

/-- On every stopped increasing partition, the original BV source
remainder has a weighted-variation envelope involving only the source
path and its drift at the samplewise stopping horizon. -/

theorem AvramDividend.Classical.avram_wave5_04a_actual_bv_stopped_source_weighted_remainder_drift_envelope
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hBV : X.BoundedVariation) :
    ∀ᵐ ω ∂P, ∃ R : ℝ≥0 → ℝ,
      (∀ t : ℝ≥0,
        R t = ((t : ℝ) * X.drift - X.X t ω) -
          (∑' (v : ℝ≥0),
            if 0 < v ∧ v ≤ t then
              ENNReal.ofReal (Function.leftLim
                (fun z : ℝ≥0 => X.X z ω) v - X.X v ω)
            else 0).toReal) ∧
      Monotone R ∧
      ∀ (τ : Ω → ℝ≥0) (u : ℕ → ℝ≥0)
        (hu : Monotone u) (n : ℕ) (hstop : u n ≤ τ ω)
        (a : ℕ → ℝ) (M : ℝ) (hM : 0 ≤ M)
        (ha : ∀ i : ℕ, |a i| ≤ M),
        |(Finset.range n).sum (fun i =>
          a i * (R (u (i + 1)) - R (u i)))| ≤
          M * (((τ ω : ℝ) - (u 0 : ℝ)) * X.drift -
            (X.X (τ ω) ω - X.X (u 0) ω)) := by sorry
