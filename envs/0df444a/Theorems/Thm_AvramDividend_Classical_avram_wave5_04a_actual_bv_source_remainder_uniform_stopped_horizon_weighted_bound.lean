-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave5_04a_actual_bv_source_remainder_uniform_stopped_horizon_weighted_bound
-- name    : AvramDividend.Classical.avram_wave5_04a_actual_bv_source_remainder_uniform_stopped_horizon_weighted_bound
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-01T12:11:31.429808+00:00
-- url     : https://prove2.me/theorems/c63f3683-faa0-4067-a6d0-142f67a74728
-- title:
--   Actual source bounded-variation remainder: uniform weighted partition bound at stopped horizon
-- statement:
--   For the actual original spectrally negative Levy source with bounded variation, almost surely the explicitly defined monotone source residual has the following uniform stopped bound: for any increasing finite partition below arbitrary samplewise stopping horizon tau, all real weights bounded in absolute value by M have residual weighted sum bounded by M times R(tau)-R(start). The bound is independent of partition length and mesh, and is a pathwise envelope for nonlinear C1 source approximation, without identifying any Ito-Meyer integral.
-- source:
--   Chat04-A original-source stopped finite-variation envelope, deduced from canonically Proved exact weighted source residual variation bound 2496fb55-e8d1-455f-9cea-0728d868c5b9 and monotonicity of the same R.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_wave5_04a_actual_bv_source_remainder_weighted_partition_absolute_variation_bound

open MeasureTheory Filter Set Topology AvramDividend.Classical
open scoped NNReal ENNReal BigOperators

/-- A partition-uniform real bound on every weighted original BV source
residual sum stopped below an arbitrary samplewise horizon. This gives
a pathwise finite-variation envelope independent of partition mesh. -/

theorem AvramDividend.Classical.avram_wave5_04a_actual_bv_source_remainder_uniform_stopped_horizon_weighted_bound
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
          M * (R (τ ω) - R (u 0)) := by sorry
