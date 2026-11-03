-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave7_06_original_intrinsic_marked_count_horizon_mono
-- name    : AvramDividend.Classical.avram_wave7_06_original_intrinsic_marked_count_horizon_mono
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-02T15:22:04.655502+00:00
-- url     : https://prove2.me/theorems/ba5f5db9-0245-496e-9a20-257f6d638453
-- title:
--   Genuine source intrinsic marked jump count increases with horizon
-- statement:
--   For every original source sample path ω and any real mark set B, the pathwise intrinsic jump counting measure of (0,S] × B is bounded by that of (0,T] × B whenever S≤T. The result is an unconditional pathwise measure monotonicity interface, without a coupling to an auxiliary Poisson process.
-- source:
--   Exact X.X and source P source-faithful horizon count helper toward original predictable marked-cell approximation.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy

open MeasureTheory Filter Set Topology AvramDividend.Classical
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_wave7_06_original_intrinsic_marked_count_horizon_mono
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (ω : Ω)
    (S T : ℝ≥0) (B : Set ℝ) (hST : S ≤ T) :
    (let NX : Ω → Measure (ℝ≥0 × ℝ) := fun ω =>
      ((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u,
          X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
     NX ω (Ioc 0 S ×ˢ B) ≤ NX ω (Ioc 0 T ×ˢ B)) := by sorry
