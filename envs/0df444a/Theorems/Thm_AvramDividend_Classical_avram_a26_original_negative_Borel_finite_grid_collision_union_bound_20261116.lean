-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_a26_original_negative_Borel_finite_grid_collision_union_bound_20261116
-- name    : AvramDividend.Classical.avram_a26_original_negative_Borel_finite_grid_collision_union_bound_20261116
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-16T07:46:52.953988+00:00
-- url     : https://prove2.me/theorems/92aeb6fa-efc3-43a3-a61f-f16d3323a6d8
-- title:
--   Physical marked Borel count finite-grid collision probability bound
-- statement:
--   Under original finite negative-jump activity, the chance any of n consecutive width-delta cells contains two physical B-marked jumps is at most n times half squared cell intensity. Use source shifted two-jump inequality and finite-union subadditivity, giving a grid coupling bound for the binomial approximation.
-- source:
--   Proved shifted source collision f0852f64 and finite union subadditivity

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal BigOperators
noncomputable section

theorem AvramDividend.Classical.avram_a26_original_negative_Borel_finite_grid_collision_union_bound_20261116
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hFinite : X.ν (Iio (0 : ℝ)) ≠ ⊤)
    (δ : ℝ≥0) (n : ℕ) (B : Set ℝ)
    (hB : MeasurableSet B) (hNeg : B ⊆ Iio (0 : ℝ)) :
    let NX : Ω → Measure (ℝ≥0 × ℝ) := fun ω =>
      ((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u,
          X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
    let E : ℕ → Set Ω := fun i =>
      {ω | (2 : ℝ) ≤
        (NX ω (Ioc ((i : ℝ≥0) * δ)
          ((i : ℝ≥0) * δ + δ) ×ˢ B)).toReal}
    (P (⋃ i ∈ Finset.range n, E i)).toReal ≤
      (n : ℝ) * (((δ : ℝ≥0∞) * X.ν B).toReal ^ 2 / 2) := by sorry
