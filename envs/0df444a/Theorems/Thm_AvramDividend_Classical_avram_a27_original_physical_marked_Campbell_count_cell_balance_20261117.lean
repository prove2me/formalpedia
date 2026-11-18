-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_a27_original_physical_marked_Campbell_count_cell_balance_20261117
-- name    : AvramDividend.Classical.avram_a27_original_physical_marked_Campbell_count_cell_balance_20261117
-- status  : Open
-- author  : @WillR
-- created : 2026-11-17T16:56:13.745041+00:00
-- url     : https://prove2.me/theorems/8103d331-e796-44fc-8517-c486d3ed9040
-- title:
--   Original physical marked jump Campbell count-cell balance on the unchanged Lévy probability space
-- statement:
--   For the actual original finite-activity spectrally negative Lévy path, the k+1 physical negative-jump exponential weighted count cell, multiplied by k+1, equals the prior cell times the original intensity r plus horizon-scaled Lévy exponential excess mark integral. This is the marked compensator/Campbell step, with no independent mark-stream construction or separate probability space.
-- source:
--   Original Lévy physical marked jump counting measure and predictable compensation/Campbell formula with the product of prior physical jump exponentials; source-faithful Mecke count factorial recursion.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open MeasureTheory ProbabilityTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal BigOperators
noncomputable section

theorem AvramDividend.Classical.avram_a27_original_physical_marked_Campbell_count_cell_balance_20261117
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hFinite : X.ν (Iio (0 : ℝ)) ≠ ⊤) (hNu : X.ν ≠ 0)
    (t : ℝ≥0) (ht : 0 < t) (θ : ℝ) (hθ : 0 < θ)
    (J : Ω → ℝ) (hJMeas : Measurable J)
    (hJEq : J =ᵐ[P] fun ω =>
      ∑' u : ℝ≥0,
        if 0 < u ∧ u ≤ t then
          X.X u ω - Function.leftLim (fun z : ℝ≥0 => X.X z ω) u
        else 0)
    (K : Ω → ℕ) (r : ℝ≥0)
    (hK : Measurable K) (hLaw : HasLaw K (poissonMeasure r) P)
    (hCount : ∀ᵐ ω ∂P, (K ω : ℝ) =
      (((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u,
          X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
        (Ioc 0 t ×ˢ Iio (0 : ℝ))).toReal)
    (hRate : (r : ℝ) =
      ((t : ℝ≥0∞) * X.ν (Iio (0 : ℝ))).toReal) :
    ∀ k : ℕ,
      (((k + 1 : ℕ) : ℝ) * (∫ ω in {ω : Ω | K ω = k + 1}, Real.exp (θ * J ω) ∂P)) =
        ((r : ℝ) + (t : ℝ) * (∫ y in Iio (0 : ℝ), Real.exp (θ * y) - 1 ∂X.ν)) * (∫ ω in {ω : Ω | K ω = k}, Real.exp (θ * J ω) ∂P) := by sorry
