-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_a27_original_physical_zero_count_laplace_cell_20261117
-- name    : AvramDividend.Classical.avram_a27_original_physical_zero_count_laplace_cell_20261117
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-17T16:10:38.084516+00:00
-- url     : https://prove2.me/theorems/745915a1-cbe3-4256-9970-ee5a7b234455
-- title:
--   Exact original physical negative jump Laplace contribution on the zero Poisson count cell
-- statement:
--   For the actual original-space spectral-negative Levy jump count K with its Poisson law, the exponential of the full physical jump sum has integral over K=0 equal to the exact zero Poisson mass, independent of any mark-stream construction.
-- source:
--   The original physical empty-count exponential theorem and the generic Poisson zero count-cell integral; no circular e22 or a104 usage.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open MeasureTheory ProbabilityTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal BigOperators
noncomputable section

theorem AvramDividend.Classical.avram_a27_original_physical_zero_count_laplace_cell_20261117
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hFinite : X.ν (Iio (0 : ℝ)) ≠ ⊤)
    (t : ℝ≥0) (θ : ℝ) (J : Ω → ℝ)
    (hJEq : J =ᵐ[P] fun ω =>
      ∑' u : ℝ≥0, if 0 < u ∧ u ≤ t then
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
        (Ioc 0 t ×ˢ Iio (0 : ℝ))).toReal) :
    (∫ ω in {ω : Ω | K ω = 0}, Real.exp (θ * J ω) ∂P) =
      (poissonMeasure r).real {0} := by sorry
