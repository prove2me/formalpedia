-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_b131_original_ae_zero_negative_counts_to_full_signed_smallmark_drift
-- name    : AvramDividend.Classical.avram_b131_original_ae_zero_negative_counts_to_full_signed_smallmark_drift
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-14T08:35:41.112199+00:00
-- url     : https://prove2.me/theorems/1df0ffe3-9a0c-4677-99dd-8f8ef4644fa7
-- title:
--   Conull original stopped zero negative-band Poisson counts give the exact signed full smallmark compensator drift
-- statement:
--   At true original random stopped source clock endpoints on a common conull event, suppose every negative reciprocal cutoff Poisson marked count is zero. The original physical B110 source count identity excludes marks of each cutoff; B130 identifies each compensated finite cutoff smallmark increment with the signed Levy compensator drift. The original B127 conull cutoff-limit transfer and Proved B84 Levy moment convergence then yield the exact full signed negative smallmark drift on the same original source and random clocks. This is a stronger source-faithful smallmark decomposition than the older B82/B85 all-path statements, without global negative second moments. Publish when all three premises are Proved.
-- source:
--   Prepared B110, B130, B127 and Proved B84, same original source almost-everywhere limit.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_avram_p4_h_gaussian_intrinsic_small_band_compensated
import Theorems.Thm_AvramDividend_Classical_avram_b110_original_negative_count_zero_forbids_actual_band_source_jump
import Theorems.Thm_AvramDividend_Classical_avram_b130_original_negative_bandfree_cell_exact_compensation_drift
import Theorems.Thm_AvramDividend_Classical_avram_b127_original_ae_smallmark_cutoff_drift_limit_transfer
open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- All original negative Poisson band counts zero at the true random clocks imply exact full compensated smallmark drift on the same conull event. -/

theorem AvramDividend.Classical.avram_b131_original_ae_zero_negative_counts_to_full_signed_smallmark_drift
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hFinite : X.ν (Iio (0 : ℝ)) ≠ ⊤)
    (Jsmall : ℝ≥0 → Ω → ℝ)
    (hJlim : ∀ᵐ ω ∂P, ∀ u : ℝ≥0,
      Tendsto
        (fun n : ℕ =>
          avram_p4_h_gaussian_intrinsic_small_band_compensated X n u ω)
        atTop (𝓝 (Jsmall u ω)))
    (s t : Ω → ℝ≥0) (hOrder : ∀ ω, s ω ≤ t ω)
    (hZero : ∀ᵐ ω ∂P, ∀ n : ℕ,
      ((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
          (fun u : ℝ≥0 => (u,
            X.X u ω -
              Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
        (Ioc (s ω) (t ω) ×ˢ Iic (-(1 / ((n : ℝ) + 1)))) = 0) :
    ∀ᵐ ω ∂P, Jsmall (t ω) ω - Jsmall (s ω) ω =
      -(∫ z in Ioo (-1 : ℝ) 0, z ∂X.ν) *
        ((t ω : ℝ) - (s ω : ℝ)) := by sorry
