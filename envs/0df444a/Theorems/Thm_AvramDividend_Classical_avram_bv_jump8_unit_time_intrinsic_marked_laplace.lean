-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_bv_jump8_unit_time_intrinsic_marked_laplace
-- name    : AvramDividend.Classical.avram_bv_jump8_unit_time_intrinsic_marked_laplace
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-06T13:11:30.172858+00:00
-- url     : https://prove2.me/theorems/7908f13f-3295-4a5d-8b0e-43fa863ac4ee
-- title:
--   Original intrinsic weighted marked-jump Laplace law on the first unit interval
-- statement:
--   For each strictly negative reciprocal cutoff, the intrinsic marked jump counting measure of the literal original spectrally negative Levy path has the exact weighted exponential Laplace functional over (0,1]. The weighted mark law, not just the jump-count Poisson distribution, must be established.
-- source:
--   Independent unit-time stochastic obligation for canonical 81b0ea8d. Derive through genuine finite-mark partition Poisson random-measure structure identified with the source process, or via a source-valid exponential martingale/compensator argument. First moments and unweighted count laws alone are insufficient.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_bv_jump8_unit_time_intrinsic_marked_laplace
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (hBV : X.BoundedVariation) :
    ∀ (k : ℕ),
      (∫ ω : Ω, Real.exp (-((∫⁻ p : ℝ≥0 × ℝ,
      if 0 < p.1 ∧ p.1 ≤ (1 : ℝ≥0) ∧
        p.2 < -(1 / ((k : ℝ) + 1)) then
        ENNReal.ofReal (-p.2) else 0
      ∂((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
          (fun u : ℝ≥0 => (u, X.X u ω -
            Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))).toReal)) ∂P) =
        Real.exp (-(∫ y in Iio (-(1 / ((k : ℝ) + 1))),
          (1 - Real.exp y) ∂X.ν)) := by sorry
