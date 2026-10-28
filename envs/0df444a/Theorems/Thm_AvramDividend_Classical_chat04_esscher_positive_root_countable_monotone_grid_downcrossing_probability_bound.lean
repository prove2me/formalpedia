-- Prove2me | Theorems.Thm_AvramDividend_Classical_chat04_esscher_positive_root_countable_monotone_grid_downcrossing_probability_bound
-- name    : AvramDividend.Classical.chat04_esscher_positive_root_countable_monotone_grid_downcrossing_probability_bound
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-27T07:14:48.986983+00:00
-- url     : https://prove2.me/theorems/a208448a-ed89-436a-aa46-8271627fa653
-- title:
--   Uniform Esscher exponential downcrossing probability bound on an entire countable bounded monotone time schedule
-- statement:
--   Let g:ℕ→ℝ≥0 be any bounded monotone observation schedule with g(k)≤T. Under the genuine terminal φ-Esscher probability law, for q>0 and positive root ψφ=q, the bound exp(φb/2)·Q_T(∃k:X_{g(k)}≤−b)≤1 holds for the *entire countably infinite observation schedule*. This is obtained without any infinite-horizon tilted law, by finite-grid Doob bounds uniform in the prefix length and measure continuity from below.
-- source:
--   Define measurable nested prefix events s_n={∃k≤n:X(g k)≤−b}. Show monotonicity and measurability using adaptedness of the Lévy process, the filtration's ambient inclusion and countable union of preimages of Ici/Iic. Use accepted `chat04_esscher_positive_root_finite_grid_downcrossing_probability_bound` for every n and accepted `uniform_weighted_finite_prefix_measure_bound_extends_to_countable_union` for the full union, identified with the countable downcrossing event by straightforward set extensionality.

import Mathlib.MeasureTheory.Measure.MeasureSpace
import Mathlib.Probability.Process.Filtration
import Mathlib.Analysis.Complex.Exponential
import Theorems.Thm_AvramDividend_Classical_chat04_esscher_positive_root_finite_grid_downcrossing_probability_bound
import Theorems.Thm_AvramDividend_Classical_uniform_weighted_finite_prefix_measure_bound_extends_to_countable_union
open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.chat04_esscher_positive_root_countable_monotone_grid_downcrossing_probability_bound
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (q φ b : ℝ) (hq : 0 < q) (hφ : 0 < φ)
    (hroot : X.ψ φ = q)
    (T : ℝ≥0) (g : ℕ → ℝ≥0) (hg : Monotone g)
    (hgT : ∀ k : ℕ, g k ≤ T)
    (a : ℝ≥0) (ha : (a : ℝ) = Real.exp ((φ / 2) * b)) :
    (a : ℝ≥0∞) *
      (P.withDensity (fun ω : Ω => ENNReal.ofReal
        (Real.exp (φ * X.X T ω - (T : ℝ) * X.ψ φ))))
        {ω : Ω | ∃ k : ℕ, X.X (g k) ω ≤ -b} ≤ 1 := by sorry
