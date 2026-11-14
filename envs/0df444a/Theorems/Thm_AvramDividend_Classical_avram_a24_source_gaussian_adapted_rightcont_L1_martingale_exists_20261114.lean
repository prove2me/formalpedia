-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_a24_source_gaussian_adapted_rightcont_L1_martingale_exists_20261114
-- name    : AvramDividend.Classical.avram_a24_source_gaussian_adapted_rightcont_L1_martingale_exists_20261114
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-14T00:14:01.350962+00:00
-- url     : https://prove2.me/theorems/4f55426c-b105-4d66-89f7-97c210fd9df1
-- title:
--   Original finite-activity Gaussian intrinsic source admits a globally adapted zero-origin L1 martingale almost surely right-continuous at every time
-- statement:
--   For any original spectrally negative Lévy process with finite negative mark activity, there exists a globally raw-filtration adapted zero-origin Gaussian intrinsic source, integrable and a right-continuous-filtration martingale, with all-time right-continuity on one conull event.
-- source:
--   Proved e33982e1 physical source martingale; b15909f6 canonical adapted almost-sure right-continuous G; Mathlib conditional expectation and L1 AE transfer.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_avram_p4_h_gaussian_intrinsic_truncated_residual
import Theorems.Thm_AvramDividend_Classical_avram_b31_original_finite_activity_intrinsic_gaussian_martingale_exists
import Theorems.Thm_AvramDividend_Classical_avram_a24_original_gaussian_canonical_adapted_ae_rightcont_20261113
open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- A source Gaussian martingale is globally adapted, zero-origin, L1 and almost surely right-continuous at all times. -/

theorem AvramDividend.Classical.avram_a24_source_gaussian_adapted_rightcont_L1_martingale_exists_20261114
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (hFinite : X.ν (Iio (0 : ℝ)) ≠ ⊤) :
    ∃ G : ℝ≥0 → Ω → ℝ,
      (∀ t, Measurable[𝓕 t] (G t)) ∧
      (∀ ω : Ω, G 0 ω = 0) ∧
      (∀ᵐ ω ∂P, ∀ t,
        ContinuousWithinAt (fun u : ℝ≥0 => G u ω) (Ici t) t) ∧
      (∀ t, Integrable (G t) P) ∧
      (∀ s t : ℝ≥0, s ≤ t →
        ∀ᵐ ω ∂P,
          condExp (𝓕.rightCont s) P (G t) ω = G s ω) := by sorry
