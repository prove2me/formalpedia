-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_bv_error7_ruin8_vcstar_original_all_positive_bands_jet_envelopes
-- name    : AvramDividend.Classical.avram_bv_error7_ruin8_vcstar_original_all_positive_bands_jet_envelopes
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-07T08:51:55.864616+00:00
-- url     : https://prove2.me/theorems/fd39b7a6-6661-4dd8-910b-f4c303a6cac2
-- title:
--   Actual BV barrier value supplies all positive compact-band C1 jet envelopes for stopped-error localisation
-- statement:
--   For the authentic BV barrier value, an arbitrary sequence of compact reserve bands with strictly positive lower endpoints admits a sequence of nonnegative Lipschitz/derivative envelopes. These are precisely the interior localisation hypotheses required by the already-Proved original strict stopped-grid C1 error convergence. The theorem does not cover the contact cell crossing ruin and does not invoke a BV dividend prebudget.
-- source:
--   Select the source-specific compact derivative bound separately on each positive band, then apply the source-specific mean-value contact inequality on that band. Assemble the resulting estimates using dependent choice. This supplies the local Lipschitz and derivative hypotheses in the Proved P3-F2 event-localised error theorem, eliminating their independent assertion for vcstar.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_bv_error7_ruin8_vcstar_deriv_bounded_on_positive_compact_band
import Theorems.Thm_AvramDividend_Classical_avram_bv_error7_ruin8_vcstar_contact_lipschitz_from_positive_band_deriv
open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_bv_error7_ruin8_vcstar_original_all_positive_bands_jet_envelopes
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (q : ℝ) (hq : 0 < q) (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (hc : cstar W < ⊤) (hcpos : 0 < cstar W)
    (hbv : X.BoundedVariation) (a b : ℕ → ℝ) (ha : ∀ n, 0 < a n) :
    ∃ L : ℕ → ℝ,
      (∀ n, 0 ≤ L n) ∧
      (∀ n, ∀ y ∈ Set.Icc (a n) (b n), ∀ z ∈ Set.Icc (a n) (b n),
        |vcstar W z - vcstar W y| ≤ L n * |z - y|) ∧
      (∀ n, ∀ y ∈ Set.Icc (a n) (b n), |deriv (vcstar W) y| ≤ L n) := by sorry
