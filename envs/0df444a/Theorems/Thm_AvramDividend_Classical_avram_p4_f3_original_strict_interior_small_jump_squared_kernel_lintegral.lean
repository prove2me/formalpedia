-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p4_f3_original_strict_interior_small_jump_squared_kernel_lintegral
-- name    : AvramDividend.Classical.avram_p4_f3_original_strict_interior_small_jump_squared_kernel_lintegral
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-05T16:44:54.764159+00:00
-- url     : https://prove2.me/theorems/109cbcce-e799-4425-974e-518ff9909454
-- title:
--   Original strict-interior small-jump quadratic Lévy kernel energy bound
-- statement:
--   For the exact original spectrally negative Lévy X and canonical interior C2 value function w, on every compact strict-positive interval of reserves inside the cap the physical negative-jump quadratic kernel integral is dominated by an explicit coefficient times squared source marks. The result is uniform across all measurable mark sets whose jumps remain inside the interval, preserves original ν and is the deterministic integrand input to the small-jump martingale L2 estimate.
-- source:
--   Use public Proved P4-F3 interior Lipschitz theorem 8179243e on both endpoints of each actual jump u→u+z. Take nonnegative absolute Lipschitz constant, square the pathwise bound, transfer to ENNReal.ofReal by the pinned monotonicity lemma, and integrate by restricted measure almost-everywhere monotonicity. The separate stochastic isometry and original stopping/localisation remain open.

import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_p4_f3_original_positive_band_lipschitz_source
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- Physical small-jump squared kernels are bounded by quadratic source-mark energy on a strict interior band. -/

theorem AvramDividend.Classical.avram_p4_f3_original_strict_interior_small_jump_squared_kernel_lintegral
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (w : ℝ → ℝ) (C : ℝ≥0∞)
    (hw_smooth : ContDiffOn ℝ 2 w
      {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (δ K : ℝ) (hδ : 0 < δ) (hδK : δ ≤ K)
    (hK : ENNReal.ofReal K < C) :
    ∃ B0 : ℝ, 0 ≤ B0 ∧ ∀ u ∈ Icc δ K,
      ∀ B : Set ℝ, MeasurableSet B →
        (∀ z ∈ B, u + z ∈ Icc δ K) →
        (∫⁻ z in B, ENNReal.ofReal ((w (u + z) - w u) ^ 2) ∂X.ν) ≤
          (∫⁻ z in B, ENNReal.ofReal ((B0 * |z|) ^ 2) ∂X.ν) := by sorry
