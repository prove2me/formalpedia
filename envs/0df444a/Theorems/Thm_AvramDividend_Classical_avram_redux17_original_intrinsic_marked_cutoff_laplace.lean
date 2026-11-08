-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_redux17_original_intrinsic_marked_cutoff_laplace
-- name    : AvramDividend.Classical.avram_redux17_original_intrinsic_marked_cutoff_laplace
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-06T11:54:39.575053+00:00
-- url     : https://prove2.me/theorems/81b0ea8d-1831-42c2-b84d-2a211d2e4a39
-- title:
--   Intrinsic marked-count finite-cutoff Laplace functional on the original BV Levy space
-- statement:
--   For the literal intrinsic marked jump-counting measure of the original spectrally negative Levy process, the exponential moment of its finite-cutoff marked magnitude integral equals the corresponding finite Levy-measure exponential compensator. This supplies the stochastic marked-point-process Laplace law independently of the separate pointwise identity between an intrinsic marked-count integral and a time-indexed actual jump sum.
-- source:
--   Faithful original-process reformulation of the stochastic ingredient in avram_redux12b_original_jump_laplace_finite_cutoff; the source-only marked-count-to-tsum result avram_wave4_04a_actual_intrinsic_lintegral_eq_jump_sum is already Proved.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_redux17_original_intrinsic_marked_cutoff_laplace
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (hBV : X.BoundedVariation) :
    ∀ (n k : ℕ),
      (∫ ω : Ω, Real.exp (-((∫⁻ p : ℝ≥0 × ℝ,
        if 0 < p.1 ∧ p.1 ≤ (n : ℝ≥0) ∧
          p.2 < -(1 / ((k : ℝ) + 1)) then
          ENNReal.ofReal (-p.2) else 0
        ∂((Measure.count.restrict {u : ℝ≥0 |
          0 < u ∧ X.X u ω -
            Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
            (fun u : ℝ≥0 => (u, X.X u ω -
              Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))).toReal)) ∂P) =
      Real.exp (-((n : ℝ) *
        (∫ y in Iio (-(1 / ((k : ℝ) + 1))), (1 - Real.exp y) ∂X.ν))) := by sorry
