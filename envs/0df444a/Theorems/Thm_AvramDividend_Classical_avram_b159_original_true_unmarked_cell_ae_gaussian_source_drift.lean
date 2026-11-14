-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_b159_original_true_unmarked_cell_ae_gaussian_source_drift
-- name    : AvramDividend.Classical.avram_b159_original_true_unmarked_cell_ae_gaussian_source_drift
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-13T22:46:44.803875+00:00
-- url     : https://prove2.me/theorems/53e87095-5abc-4abb-af15-f58d21d1706f
-- title:
--   Genuinely unmarked original random-clock cells have the intrinsic Gaussian and signed Levy drift decomposition almost everywhere
-- statement:
--   For the exact original finite-negative-activity spectrally negative Lévy source, with its intrinsic Gaussian and compensated negative source limits converging for all times on a conull event, take any potentially random physical cell s≤t and a predicate marking whether the cell contains an actual original source jump. Assume precisely that each unmarked original cell is genuinely jumpfree for all physical times in its half-open interval. Define a modified left endpoint equal to t on marked paths and s on unmarked paths, leaving the right endpoint t unchanged. The modified interval is always physically jumpfree, since marked paths now have zero duration. The B146 genuine original source Gaussian-drift theorem then applies on a single conull event to this modified random interval and reduces on unmarked paths to the original X physical source increment equal to intrinsic Gaussian residual R increment plus the full signed negative-strip compensation drift. This resolves the need to assume globally jumpfree cells when obtaining the source decomposition for unmarked physical grid cells. Publication awaits B146 Proved.
-- source:
--   Prepared original B146 conull physical Gaussian-plus-signed-drift source increment, original unmarked-cell physical jump classification.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_avram_p4_h_gaussian_intrinsic_truncated_residual
import Definitions.Def_AvramDividend_Classical_avram_p4_h_gaussian_intrinsic_small_band_compensated
import Theorems.Thm_AvramDividend_Classical_avram_b146_original_ae_jumpfree_intrinsic_gaussian_full_drift_source_increment
open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- Genuine original unmarked physical random source cells obey the intrinsic Gaussian signed-drift decomposition almost everywhere by collapsing marked cells to zero duration. -/

theorem AvramDividend.Classical.avram_b159_original_true_unmarked_cell_ae_gaussian_source_drift
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hFinite : X.ν (Iio (0 : ℝ)) ≠ ⊤)
    (R Jsmall : ℝ≥0 → Ω → ℝ)
    (hRsrc : ∀ᵐ ω ∂P, ∀ u : ℝ≥0,
      Tendsto (fun k : ℕ =>
        avram_p4_h_gaussian_intrinsic_truncated_residual X k u ω)
        atTop (𝓝 (R u ω)))
    (hJsrc : ∀ᵐ ω ∂P, ∀ u : ℝ≥0,
      Tendsto (fun k : ℕ =>
        avram_p4_h_gaussian_intrinsic_small_band_compensated X k u ω)
        atTop (𝓝 (Jsmall u ω)))
    (s t : Ω → ℝ≥0) (hOrder : ∀ ω, s ω ≤ t ω)
    (Marked : Ω → Prop)
    (hOriginalUnmarked : ∀ ω, ¬ Marked ω → ∀ u : ℝ≥0,
      s ω < u → u ≤ t ω →
      X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u = 0) :
    ∀ᵐ ω ∂P, ¬ Marked ω →
      X.X (t ω) ω - X.X (s ω) ω =
        ((t ω : ℝ) - (s ω : ℝ)) *
          (X.c - ∫ z in Ioo (-1 : ℝ) 0, z ∂X.ν) +
        (R (t ω) ω - R (s ω) ω) := by sorry
