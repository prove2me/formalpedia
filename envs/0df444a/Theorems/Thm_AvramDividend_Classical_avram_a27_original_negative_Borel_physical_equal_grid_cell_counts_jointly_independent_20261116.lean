-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_a27_original_negative_Borel_physical_equal_grid_cell_counts_jointly_independent_20261116
-- name    : AvramDividend.Classical.avram_a27_original_negative_Borel_physical_equal_grid_cell_counts_jointly_independent_20261116
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-16T09:23:15.106531+00:00
-- url     : https://prove2.me/theorems/6b099ff9-7e24-4cea-97da-ba0c1b65f37e
-- title:
--   Original physical Borel marked jump counts on a finite equal-time grid form a jointly independent family
-- statement:
--   For any finite equal-width deterministic grid on the original spectrally negative Lévy process, the actual physical Borel marked-jump counts over the disjoint consecutive half-open cells are jointly independent random variables under the original P. Derive mutual finite-family independence from independent increments / original future physical Borel count independent of every measurable past observable (Proved 0832c67e), including measurability of each count in its terminal original filtration. The original Ω, P, filtration and physical jump counting measure must be retained, no Poisson companion process or transported substitute.
-- source:
--   Original future physical marked-count independent of arbitrary measurable past observable 0832c67e; original physical rectangle-count measurability 8146a449; original Lévy filtration adaptedness.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open MeasureTheory ProbabilityTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal BigOperators
noncomputable section

theorem AvramDividend.Classical.avram_a27_original_negative_Borel_physical_equal_grid_cell_counts_jointly_independent_20261116
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (T : ℝ≥0) (B : Set ℝ) (hB : MeasurableSet B)
    (n : ℕ) :
    let NX : Ω → Measure (ℝ≥0 × ℝ) := fun ω =>
      ((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u,
          X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
    let δ : ℝ≥0 := T / (n : ℝ≥0)
    iIndepFun (fun i : Fin n => fun ω : Ω =>
      NX ω (Ioc ((i.val : ℝ≥0) * δ)
        (((i.val + 1 : ℕ) : ℝ≥0) * δ) ×ˢ B)) P := by sorry
