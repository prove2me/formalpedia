-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p4_f_assembly_original_grid_pair_lintegral_finite_sum
-- name    : AvramDividend.Classical.avram_p4_f_assembly_original_grid_pair_lintegral_finite_sum
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-04T13:07:01.925231+00:00
-- url     : https://prove2.me/theorems/21debe40-9ac3-4ee1-880e-d5d00ba61a63
-- title:
--   Finite original-source chronological marked pair cross-count sum commutes with ENNReal expectation
-- statement:
--   For a finite deterministic collection of original same-path marked negative jump-count windows, the ENNReal expectation of the sum of past-count times future-count products equals the sum of their ENNReal expectations. Both count factors refer to the unchanged original spectrally negative Lévy process and natural filtration. This is the finite-grid measure-theoretic exchange needed to combine separately proved original cross-window compensator means before grid refinement, with no extra measurability or integrability premises: both factors are original measurable marked-rectangle counts.

import Mathlib.MeasureTheory.Measure.Count
import Mathlib.Topology.Order.LeftRightLim
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_p2_d_future_intrinsic_marked_rectangle_measurable
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal BigOperators
noncomputable section

theorem AvramDividend.Classical.avram_p4_f_assembly_original_grid_pair_lintegral_finite_sum
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (m : ℕ) (s t : Fin m → ℝ≥0) (n : ℕ) :
    let B : Set ℝ := Iic (-(1 / ((n : ℝ) + 1)))
    let N : ℝ≥0 → ℝ≥0 → Ω → ℝ≥0∞ := fun a b ω =>
      ((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u,
          X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
        (Ioc a b ×ˢ B)
    (∫⁻ ω, ∑ i : Fin m, N 0 (s i) ω * N (s i) (t i) ω ∂P) =
      ∑ i : Fin m, ∫⁻ ω, N 0 (s i) ω * N (s i) (t i) ω ∂P := by sorry
