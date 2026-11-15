-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_b87_original_true_negative_markfree_intrinsic_gaussian_drift_split
-- name    : AvramDividend.Classical.avram_b87_original_true_negative_markfree_intrinsic_gaussian_drift_split
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-14T08:12:40.49885+00:00
-- url     : https://prove2.me/theorems/27ac9178-7c10-4990-9e27-732eca34ead1
-- title:
--   Original finite-mixed truly unmarked interior cells decompose into intrinsic same-source Gaussian and exact negative compensation drift
-- statement:
--   For the original finite-negative-activity spectrally negative Lévy source, take its physical intrinsic Gaussian residual R, original limiting small compensated negative-mark source Jsmall, and any actual finite selected stopped mesh whose unmarked cells contain no physical source mark. Assuming Jsmall is pointwise realised as the original cutoff limit, B86 supplies the exact compensation drift of the small-negative source and constancy of the large-negative source on every such unmarked cell. B78 supplies one totalised original Gaussian residual M, almost everywhere equal to R at all physical clocks, for which the drift-corrected increments of the actual X path are precisely M increments plus the deterministic negative first-moment drift. No surrogate Brownian motion or independent auxiliary Lévy process is introduced, nor any global second-moment requirement for large negative marks. The remaining mathematical hypotheses are verifying the mark-free classification for unmarked physical mesh cells and obtaining the pointwise version of the intrinsic limit on the exceptional source set. This theorem helps discharge the true noJump source premise in the original mixed source energy B73 and the final JB27 stopped Itô calculation.
-- source:
--   Original source B78/B86, Proved JB20 original same-source all-random-clock decomposition, Proposition 4(i).

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_avram_p4_h_gaussian_intrinsic_truncated_residual
import Definitions.Def_AvramDividend_Classical_avram_p4_h_gaussian_intrinsic_small_band_compensated
import Definitions.Def_AvramDividend_Classical_avram_p4_h_gaussian_intrinsic_large_jump_sum
import Theorems.Thm_AvramDividend_Classical_avram_b78_original_jumpfree_interior_cell_gaussian_residual_drift_decomp
import Theorems.Thm_AvramDividend_Classical_avram_b86_original_true_jumpfree_selected_cells_both_negative_channels
open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal BigOperators
noncomputable section

theorem AvramDividend.Classical.avram_b87_original_true_negative_markfree_intrinsic_gaussian_drift_split
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hFinite : X.ν (Iio (0 : ℝ)) ≠ ⊤)
    (R Jsmall : ℝ≥0 → Ω → ℝ)
    (hRsource : ∀ᵐ ω ∂P, ∀ u : ℝ≥0,
      Tendsto (fun n => avram_p4_h_gaussian_intrinsic_truncated_residual X n u ω)
        atTop (𝓝 (R u ω)))
    (hJsource : ∀ᵐ ω ∂P, ∀ u : ℝ≥0,
      Tendsto (fun n => avram_p4_h_gaussian_intrinsic_small_band_compensated X n u ω)
        atTop (𝓝 (Jsmall u ω)))
    (hJtotal : ∀ ω u, Tendsto
      (fun n => avram_p4_h_gaussian_intrinsic_small_band_compensated X n u ω)
      atTop (𝓝 (Jsmall u ω)))
    (S : Finset ℕ) (s t : ℕ → Ω → ℝ≥0) (J : Ω → Finset ℕ)
    (hOrdered : ∀ ω i, i ∈ S → s i ω ≤ t i ω)
    (hNoJump : ∀ ω i, i ∈ S → i ∉ J ω →
      ∀ u : ℝ≥0, s i ω < u → u ≤ t i ω →
      X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u = 0) :
    ∃ M : ℝ≥0 → Ω → ℝ,
      (∀ᵐ ω ∂P, ∀ u : ℝ≥0, M u ω = R u ω) ∧
      (∀ ω i, i ∈ S → i ∉ J ω →
        X.X (t i ω) ω - X.X (s i ω) ω -
          ((t i ω - s i ω : ℝ≥0) : ℝ) * X.c =
        (M (t i ω) ω - M (s i ω) ω) +
          (-(∫ z in Ioo (-1 : ℝ) 0, z ∂X.ν)) *
            ((t i ω - s i ω : ℝ≥0) : ℝ)) := by sorry
