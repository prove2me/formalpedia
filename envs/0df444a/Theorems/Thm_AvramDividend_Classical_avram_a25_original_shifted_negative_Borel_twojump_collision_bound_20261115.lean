-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_a25_original_shifted_negative_Borel_twojump_collision_bound_20261115
-- name    : AvramDividend.Classical.avram_a25_original_shifted_negative_Borel_twojump_collision_bound_20261115
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-15T15:07:59.737284+00:00
-- url     : https://prove2.me/theorems/f0852f64-28da-4663-8cfd-34c1272bfd8b
-- title:
--   Quadratic two-jump collision probability on any shifted physical Lévy interval and arbitrary negative Borel mark set
-- statement:
--   For any s,T≥0 and arbitrary negative Borel marks B of finite intensity, the original physical count on (s,s+T] has collision probability at most (Tν(B))²/2 under the original P. The already-Proved original marked-count stationary-law theorem transports its distribution to the origin interval, while the original source collision inequality controls the origin distribution. This provides a uniform quadratic Bernoulli-cell error at every deterministic grid cell without constructing any companion Poisson process.
-- source:
--   Proved original physical marked count stationary law 37abf3aa, original measurable Borel marked counts 5cb1e247; newly submitted source origin two-jump collision bound 4ced9f55.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open MeasureTheory ProbabilityTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_a25_original_shifted_negative_Borel_twojump_collision_bound_20261115
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hFinite : X.ν (Iio (0 : ℝ)) ≠ ⊤)
    (s T : ℝ≥0) (B : Set ℝ)
    (hB : MeasurableSet B) (hNeg : B ⊆ Iio (0 : ℝ)) :
    let NX : Ω → Measure (ℝ≥0 × ℝ) := fun ω =>
      ((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u,
          X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
    let r : ℝ := ((T : ℝ≥0∞) * X.ν B).toReal
    (P {ω | (2 : ℝ) ≤ (NX ω (Ioc s (s + T) ×ˢ B)).toReal}).toReal ≤
      r ^ 2 / 2 := by sorry
