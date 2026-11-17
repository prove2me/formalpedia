-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_a26_physical_void_probability_parameter_rate_20261116
-- name    : AvramDividend.Classical.avram_a26_physical_void_probability_parameter_rate_20261116
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-16T07:53:35.504688+00:00
-- url     : https://prove2.me/theorems/276c9bc7-34a8-497c-9f8e-2ed73c151d9b
-- title:
--   Original negative Borel physical void probability determines the grid Bernoulli rate
-- statement:
--   For the original physical negative Borel jump count, if the occupied-cell Bernoulli probability is exactly one minus the source physical void probability on (0,T/n], then n times that probability tends to T times the actual Lévy measure of B. This identifies the source rate needed for the binomial-grid approximation using the Proved small-time physical void slope.
-- source:
--   Avram original physical void small-time rate, proved theorem 525f1cfe; direct rewrite of Bernoulli parameter.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal BigOperators
noncomputable section

theorem AvramDividend.Classical.avram_a26_physical_void_probability_parameter_rate_20261116
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hFinite : X.ν (Iio (0 : ℝ)) ≠ ⊤)
    (T : ℝ≥0) (B : Set ℝ)
    (hB : MeasurableSet B) (hNeg : B ⊆ Iio (0 : ℝ))
    (p : ℕ → unitInterval)
    (hp : ∀ n : ℕ, (p n : ℝ) =
      1 - (P {ω : Ω |
        ((Measure.count.restrict {u : ℝ≥0 |
          0 < u ∧ X.X u ω -
            Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
          (fun u : ℝ≥0 => (u, X.X u ω -
            Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
          (Ioc 0 (T / (n : ℝ≥0)) ×ˢ B) = 0}).toReal) :
    Tendsto (fun n : ℕ => (n : ℝ) * (p n : ℝ))
      atTop (𝓝 ((T : ℝ) * (X.ν B).toReal)) := by sorry
