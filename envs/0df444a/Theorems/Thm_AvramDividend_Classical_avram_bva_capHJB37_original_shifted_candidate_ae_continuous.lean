-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_bva_capHJB37_original_shifted_candidate_ae_continuous
-- name    : AvramDividend.Classical.avram_bva_capHJB37_original_shifted_candidate_ae_continuous
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-13T14:18:58.686215+00:00
-- url     : https://prove2.me/theorems/01a722f4-8b2b-4b69-8abd-bc0ccd7deb60
-- title:
--   Original bounded variation Lévy atomlessness removes exceptional zero reserve from cap-shifted candidate continuity
-- statement:
--   The actual Standing BV spectrally negative Levy measure is diffuse, so for any fixed cap and candidate function continuous outside reserve zero, the shifted candidate is continuous at cap plus negative jump for almost every original negative Levy mark. This permits a nonzero value w(0) without spuriously assuming candidate continuous at zero; it is an explicit hypothesis needed for the original full unmasked jump-rate DCT theorem.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_bvb_phys107_Standing_BV_negative_mark_singletons_null
open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

theorem AvramDividend.Classical.avram_bva_capHJB37_original_shifted_candidate_ae_continuous
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hStanding : X.Standing) (hBV : X.BoundedVariation)
    (w : ℝ → ℝ)
    (hAway : ∀ r : ℝ, r ≠ 0 → ContinuousAt w r)
    (c : ℝ) :
    ∀ᵐ z ∂(X.ν.restrict (Iio (0 : ℝ))),
      ContinuousAt w (c + z) := by sorry
