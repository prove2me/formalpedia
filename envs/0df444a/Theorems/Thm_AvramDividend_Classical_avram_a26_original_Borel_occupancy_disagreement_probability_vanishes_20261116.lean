-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_a26_original_Borel_occupancy_disagreement_probability_vanishes_20261116
-- name    : AvramDividend.Classical.avram_a26_original_Borel_occupancy_disagreement_probability_vanishes_20261116
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-16T08:13:42.615178+00:00
-- url     : https://prove2.me/theorems/7cfaa938-5fdb-4f3d-baa1-7a410360d3f2
-- title:
--   Original physical marked jump count and occupied grid count have vanishing disagreement probability
-- statement:
--   The actual marked negative jump count and its occupied equal-grid cell count disagree with probability tending to zero on the original Omega and P. The accepted original physical-count collision reduction c27 bounds this disagreement by n times the square of the intensity of one T/n cell, and the elementary quadratic grid limit proves convergence to zero. This isolates the source coupling step for the Poisson singleton limit.
-- source:
--   Original physical count collision reduction c27f305b plus quadratic uniform-cell limit a26 and the original Levy source intensity.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal BigOperators
noncomputable section

theorem AvramDividend.Classical.avram_a26_original_Borel_occupancy_disagreement_probability_vanishes_20261116
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hFinite : X.ν (Iio (0 : ℝ)) ≠ ⊤)
    (T : ℝ≥0) (B : Set ℝ)
    (hB : MeasurableSet B) (hNeg : B ⊆ Iio (0 : ℝ))
    (K : Ω → ℕ) (hK : Measurable K)
    (hCount : ∀ᵐ ω ∂P, (K ω : ℝ) =
      (((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u,
          X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
        (Ioc 0 T ×ˢ B)).toReal) :
    let NX : Ω → Measure (ℝ≥0 × ℝ) := fun ω =>
      ((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u,
          X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
    let δ : ℕ → ℝ≥0 := fun n => T / (n : ℝ≥0)
    let Z : ℕ → Ω → ℕ := fun n ω =>
      ((Finset.range n).filter (fun i : ℕ =>
        NX ω (Ioc ((i : ℝ≥0) * δ n)
          (((i + 1 : ℕ) : ℝ≥0) * δ n) ×ˢ B) ≠ 0)).card
    Tendsto (fun n : ℕ => (P {ω : Ω | K ω ≠ Z n ω}).toReal)
      atTop (𝓝 (0 : ℝ)) := by sorry
