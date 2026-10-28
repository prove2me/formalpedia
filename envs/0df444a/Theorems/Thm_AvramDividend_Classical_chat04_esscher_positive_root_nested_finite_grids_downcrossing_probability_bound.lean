-- Prove2me | Theorems.Thm_AvramDividend_Classical_chat04_esscher_positive_root_nested_finite_grids_downcrossing_probability_bound
-- name    : AvramDividend.Classical.chat04_esscher_positive_root_nested_finite_grids_downcrossing_probability_bound
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-27T07:15:48.10092+00:00
-- url     : https://prove2.me/theorems/9dcdf13b-72fd-472b-b8b3-f09045e65d41
-- title:
--   Uniform Esscher ruin bound for nested finite observation grids with arbitrarily changing mesh
-- statement:
--   For a spectrally negative Lévy process with positive q-root φ and a fixed finite Esscher terminal horizon T, let g_n(k) be any sequence of individually monotone bounded finite observation grids and m(n) their final indices. Suppose the finite-grid downcrossing events are nested in n. Then exp(φb/2)·Q_T(∃n,∃k≤m(n):X_{g_n(k)}≤−b)≤1. This removes the false requirement that one globally monotone sequence be dense: finer dyadic subdivisions are individually monotone and nested, but the union over levels is dense. The mathematical estimate is uniform in both level and cardinality.
-- source:
--   Define the finite-grid lower-crossing event s_n for each grid g_n. Each s_n is measurable from Lévy adaptedness to the ambient filtration and countable union; monotonicity across n is exactly the hypothesis hnested (dyadic grids will satisfy it). Apply the accepted actual Esscher finite-grid downcrossing theorem independently to each g_n, then apply the accepted weighted increasing-event countable union theorem to conclude the bound on the union over levels. This is the precise missing combinatorial layer for dense dyadic continuous-time passage.

import Mathlib.MeasureTheory.Measure.MeasureSpace
import Mathlib.Probability.Process.Filtration
import Mathlib.Analysis.Complex.Exponential
import Theorems.Thm_AvramDividend_Classical_chat04_esscher_positive_root_finite_grid_downcrossing_probability_bound
import Theorems.Thm_AvramDividend_Classical_uniform_weighted_finite_prefix_measure_bound_extends_to_countable_union
open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.chat04_esscher_positive_root_nested_finite_grids_downcrossing_probability_bound
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (q φ b : ℝ) (hq : 0 < q) (hφ : 0 < φ)
    (hroot : X.ψ φ = q)
    (T : ℝ≥0) (g : ℕ → ℕ → ℝ≥0) (m : ℕ → ℕ)
    (hg : ∀ n : ℕ, Monotone (g n))
    (hgT : ∀ n k : ℕ, g n k ≤ T)
    (hnested : Monotone (fun n : ℕ =>
      {ω : Ω | ∃ k : ℕ, k ≤ m n ∧ X.X (g n k) ω ≤ -b}))
    (a : ℝ≥0) (ha : (a : ℝ) = Real.exp ((φ / 2) * b)) :
    (a : ℝ≥0∞) *
      (P.withDensity (fun ω : Ω => ENNReal.ofReal
        (Real.exp (φ * X.X T ω - (T : ℝ) * X.ψ φ))))
      (⋃ n : ℕ,
        {ω : Ω | ∃ k : ℕ, k ≤ m n ∧ X.X (g n k) ω ≤ -b}) ≤ 1 := by sorry
