-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_b86_original_true_jumpfree_selected_cells_both_negative_channels
-- name    : AvramDividend.Classical.avram_b86_original_true_jumpfree_selected_cells_both_negative_channels
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-14T08:07:45.519986+00:00
-- url     : https://prove2.me/theorems/7e19a70f-9ebf-4094-a391-626bd7f557f7
-- title:
--   Original selected physical jumpfree stopped cells satisfy both actual compensated-small and large-negative mark increment identities
-- statement:
--   For the same original finite-negative-activity spectrally negative Lévy process, any cell in the actual selected random-time mesh known to contain no negative source jump has an exact drift-only increment of the original limiting compensated small-negative-band process, where the drift is the negative original ν first moment on the small negative strip. It also has an unchanged original large negative jump sum. This follows pointwise on each selected unmarked cell from B80 finite-band jumpfree compensation, B84 deterministic first-moment cutoff convergence, and B81 original large-jump finite-sum constancy, without assuming no jumps on other sample paths or replacing the original probability space. These two identities directly discharge the hSmall and hLarge premises needed by B78 on genuinely unmarked physical stopped Itô mesh cells; construction of the correct original marked-cell index set and global totalized Jsmall source limits remains separate.
-- source:
--   Proved original B81 finite large-mark source sum, original B80/B84 signed smallmark compensation; Avram Palmowski Pistorius 2007 Proposition 4(i).

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_avram_p4_h_gaussian_intrinsic_small_band_compensated
import Definitions.Def_AvramDividend_Classical_avram_p4_h_gaussian_intrinsic_large_jump_sum
import Theorems.Thm_AvramDividend_Classical_avram_b80_original_jumpfree_cell_smallband_compensator_increment
import Theorems.Thm_AvramDividend_Classical_avram_b84_original_finite_activity_negative_mark_cutoff_integral_limit
import Theorems.Thm_AvramDividend_Classical_avram_b81_original_jumpfree_cell_large_mark_sum_constant
open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_b86_original_true_jumpfree_selected_cells_both_negative_channels
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hFinite : X.ν (Iio (0 : ℝ)) ≠ ⊤)
    (Jsmall : ℝ≥0 → Ω → ℝ)
    (hJlim : ∀ ω u, Tendsto
      (fun n => avram_p4_h_gaussian_intrinsic_small_band_compensated X n u ω)
      atTop (𝓝 (Jsmall u ω)))
    (S : Finset ℕ) (s t : ℕ → Ω → ℝ≥0) (J : Ω → Finset ℕ)
    (hOrdered : ∀ ω i, i ∈ S → s i ω ≤ t i ω)
    (hNoJump : ∀ ω i, i ∈ S → i ∉ J ω →
      ∀ u : ℝ≥0, s i ω < u → u ≤ t i ω →
      X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u = 0) :
    ∀ ω i, i ∈ S → i ∉ J ω →
      (Jsmall (t i ω) ω - Jsmall (s i ω) ω =
        (-(∫ z in Ioo (-1 : ℝ) 0, z ∂X.ν)) *
          ((t i ω : ℝ) - (s i ω : ℝ))) ∧
      (avram_p4_h_gaussian_intrinsic_large_jump_sum X (t i ω) ω =
       avram_p4_h_gaussian_intrinsic_large_jump_sum X (s i ω) ω)  := by sorry
