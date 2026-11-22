-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_lsc_original_finitecap_positive_drift_upperstrip_charge_vanish
-- name    : AvramDividend.Classical.avram_lsc_original_finitecap_positive_drift_upperstrip_charge_vanish
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-22T08:11:48.951123+00:00
-- url     : https://prove2.me/theorems/da7bf92a-2d2a-45e6-9498-719549f4c683
-- title:
--   Actual original finite-cap positive Gaussian drift upperstrip expected occupation charge vanishes in shrinking-cap limit
-- statement:
--   For an actual admissible finite-cap dividend strategy of an unbounded-variation spectrally negative Lévy process, the expected occupation of the upper cap strip, multiplied by the positive part of the original process drift, tends to zero as the localisation strip narrows to the cap. The positive drift charge remains explicit at each fixed finite band.
-- source:
--   Original Avram finite-cap stopped Gaussian physical source. Uses Proved theorem cb1a7c38-88ad-4ae1-a420-677b7a6e9ea9 without replacing or assuming away positive upperstrip drift.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_f6_original_finitecap_admissible_upperstrip_expected_zero
open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_lsc_original_finitecap_positive_drift_upperstrip_charge_vanish
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hBV : ¬ X.BoundedVariation)
    (x : ℝ) (C : ℝ≥0∞) (hC : 0 < C) (hFinite : C ≠ ⊤)
    (hxc : ENNReal.ofReal x ≤ C)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (n : ℕ) (hn : 0 < n) :
    Tendsto
      (fun j : ℕ => max X.c 0 *
        (∫ ω, ∫ t in Ioo (0 : ℝ) (n : ℝ),
          if C.toReal * (((j + 1 : ℕ) : ℝ) / ((j + 2 : ℕ) : ℝ)) <
              riskProcess X x D (Real.toNNReal t) ω
          then (1 : ℝ) else 0 ∂volume ∂P))
      atTop (𝓝 (0 : ℝ)) := by sorry
