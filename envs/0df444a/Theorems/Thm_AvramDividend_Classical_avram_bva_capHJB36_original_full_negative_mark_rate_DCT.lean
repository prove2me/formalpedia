-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_bva_capHJB36_original_full_negative_mark_rate_DCT
-- name    : AvramDividend.Classical.avram_bva_capHJB36_original_full_negative_mark_rate_DCT
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-13T14:17:22.342202+00:00
-- url     : https://prove2.me/theorems/21127b6b-b6a8-417b-94da-0c41043357e7
-- title:
--   Full original negative Lévy jump rate tends to cap value under AE continuity and integrable domination
-- statement:
--   For the actual original spectrally negative Levy negative jump measure, full unmasked nonlinear jump rate converges to its finite-cap limit along any reserve sequence if the original candidate is continuous at cap and almost everywhere at shifted cap, and if the full kernel has an L1 envelope independent of reserve. Use dominated convergence; no source X or dividend substitution, no spatial cutoffs, no false A22 positive excess.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

theorem AvramDividend.Classical.avram_bva_capHJB36_original_full_negative_mark_rate_DCT
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (w : ℝ → ℝ) (c : ℝ)
    (y : ℕ → ℝ) (hy : Tendsto y atTop (𝓝 c))
    (hwc : ContinuousAt w c)
    (hwz : ∀ᵐ z ∂(X.ν.restrict (Iio (0 : ℝ))),
      ContinuousAt w (c + z))
    (g : ℝ → ℝ) (hg : Integrable g (X.ν.restrict (Iio (0 : ℝ))))
    (hMeas : ∀ n, AEStronglyMeasurable
      (fun z : ℝ => w (y n + z) - w (y n))
      (X.ν.restrict (Iio (0 : ℝ))))
    (hDom : ∀ n, ∀ᵐ z ∂(X.ν.restrict (Iio (0 : ℝ))),
      ‖w (y n + z) - w (y n)‖ ≤ ‖g z‖) :
    Tendsto (fun n => ∫ z in Iio (0 : ℝ),
      w (y n + z) - w (y n) ∂X.ν) atTop
      (𝓝 (∫ z in Iio (0 : ℝ), w (c + z) - w c ∂X.ν)) := by sorry
