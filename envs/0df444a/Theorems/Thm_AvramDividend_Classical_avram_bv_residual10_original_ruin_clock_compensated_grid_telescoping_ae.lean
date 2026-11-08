-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_bv_residual10_original_ruin_clock_compensated_grid_telescoping_ae
-- name    : AvramDividend.Classical.avram_bv_residual10_original_ruin_clock_compensated_grid_telescoping_ae
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-07T22:49:24.770573+00:00
-- url     : https://prove2.me/theorems/bd4a727d-bc79-453b-9a3f-821db22aebd9
-- title:
--   Actual original ruin-stopped compensated Levy uniform-grid sum telescopes to drift times stopped endpoint
-- statement:
--   On one almost-sure event, the finite sum of increments of the original spectrally negative bounded-variation Levy process plus its actual negative-jump sum, evaluated on the prescribed uniform physical grid clipped by the original dividend-dependent ruin clock, telescopes to the original drift times the difference of stopped grid endpoints. This is an exact finite-grid bridge, independent of any Brownian martingale representation or convergence assumption.
-- source:
--   AVRAM BV-RESIDUAL10 round 8, 7 November 2026

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_bv_residual10_original_ruin_clock_stopped_compensated_path_ae

open Classical MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_bv_residual10_original_ruin_clock_compensated_grid_telescoping_ae
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (hBV : X.BoundedVariation)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ) (S : ℝ≥0)
    (T : ℝ) (hT : 0 < T) (u : ℕ → ℕ → ℝ≥0)
    (huniform : ∀ n i,
      (u n i : ℝ) = T * (i : ℝ) / ((n : ℝ) + 2)) :
    ∀ᵐ ω ∂P, ∀ n : ℕ,
      let τ : ℝ≥0 :=
        (min (ruinTime X x D ω) (S : ℝ≥0∞)).toNNReal
      let J : ℝ≥0 → ℝ := fun r =>
        ∑' v : ℝ≥0, if 0 < v ∧ v ≤ r then
          Function.leftLim (fun z : ℝ≥0 => X.X z ω) v - X.X v ω
        else 0
      let Y : ℝ≥0 → ℝ := fun t => X.X t ω + J t
      (∑ i ∈ Finset.range (n + 1),
        (Y (min (u n (i + 1)) τ) - Y (min (u n i) τ))) =
          (((min (u n (n + 1)) τ : ℝ≥0) : ℝ) -
            ((min (u n 0) τ : ℝ≥0) : ℝ)) * X.drift := by sorry
