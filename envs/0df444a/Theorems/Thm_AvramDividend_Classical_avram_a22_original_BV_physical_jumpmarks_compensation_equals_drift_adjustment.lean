-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_a22_original_BV_physical_jumpmarks_compensation_equals_drift_adjustment
-- name    : AvramDividend.Classical.avram_a22_original_BV_physical_jumpmarks_compensation_equals_drift_adjustment
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-13T14:22:32.05875+00:00
-- url     : https://prove2.me/theorems/891842bf-e966-4bec-8b3e-3febe3f08b24
-- title:
--   Original physical negative-mark sum and compensated limit equal BV drift correction minus actual left-jump magnitudes
-- statement:
--   Derive a physical source identity on the original process: the actual uncompensated large-negative-jump integral plus the limit of the compensated small-negative-jump integral equals t times (original BV drift minus Lévy c) minus the complete original left-limit jump magnitude series. The proof must identify the actual marked counting-measure atoms and their compensator on the exact original Ω,P,filtration and use the BV drift convention. This is the substantive Lévy–Itô compensation step independent of the Gaussian residual theorem and avoids circular Gaussian-source reasoning.
-- source:
--   Avram Palmowski Pistorius (2007) Proposition 4(i); Kyprianou Lévy–Itô decomposition and finite activity; Proved dcda0213 original physical drift-and-jump path and actual definition of compensated mark measure.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_avram_p4_h_gaussian_intrinsic_large_jump_sum
import Definitions.Def_AvramDividend_Classical_avram_p4_h_gaussian_intrinsic_small_band_compensated
open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

theorem AvramDividend.Classical.avram_a22_original_BV_physical_jumpmarks_compensation_equals_drift_adjustment
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (hBV : X.BoundedVariation)
    (hFinite : X.ν (Iio (0 : ℝ)) ≠ ⊤)
    (Jsmall : ℝ≥0 → Ω → ℝ)
    (hJ : ∀ᵐ ω ∂P, ∀ t : ℝ≥0,
      Tendsto (fun k : ℕ =>
        avram_p4_h_gaussian_intrinsic_small_band_compensated X k t ω)
        atTop (𝓝 (Jsmall t ω))) :
    ∀ᵐ ω ∂P, ∀ t : ℝ≥0,
      avram_p4_h_gaussian_intrinsic_large_jump_sum X t ω +
        Jsmall t ω =
      (t : ℝ) * (X.drift - X.c) -
        (∑' u : ℝ≥0, if 0 < u ∧ u ≤ t then
          Function.leftLim (fun z : ℝ≥0 => X.X z ω) u - X.X u ω else 0) := by sorry
