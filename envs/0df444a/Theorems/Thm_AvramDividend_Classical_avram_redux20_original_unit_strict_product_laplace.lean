-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_redux20_original_unit_strict_product_laplace
-- name    : AvramDividend.Classical.avram_redux20_original_unit_strict_product_laplace
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-07T09:16:08.184388+00:00
-- url     : https://prove2.me/theorems/426d59e1-6d93-4483-88da-1134018e4034
-- title:
--   Original BV unit-time finite strict-jump exponential product has the marked Poisson Laplace expectation
-- statement:
--   The literal original spectrally negative Lévy path, restricted to its finitely many negative jumps exceeding a reciprocal cutoff on the unit interval, has an exponential product whose true expectation matches the Lévy measure marked-jump Laplace compensator. This is the genuine joint negative-mark Poisson law required after the now-Proved pathwise intrinsic integral-to-finite-product identity. A single-mark count law or first moment is insufficient.
-- source:
--   Requires the joint Poisson point-process law for the original finite strict negative jump marks. Prove via independent disjoint Borel mark-bin counts with their exact Poisson probability generating functions, then monotone simple-mark partition approximation. The statement is left as a source-exact Open stochastic child, not asserted proved by its publication.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_redux19_original_strict_negative_marked_times_finite
open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal BigOperators
noncomputable section

theorem AvramDividend.Classical.avram_redux20_original_unit_strict_product_laplace
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (hBV : X.BoundedVariation) (k : ℕ) :
    (∫ ω : Ω, ∏ u ∈
      (avram_redux19_original_strict_negative_marked_times_finite X ω (1 : ℝ≥0) k).toFinset,
      Real.exp (X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u) ∂P) =
    Real.exp (-(∫ y in Iio (-(1 / ((k : ℝ) + 1))),
      (1 - Real.exp y) ∂X.ν)) := by sorry
