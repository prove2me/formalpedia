-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_f6_original_finitecap_admissible_upperstrip_expected_zero
-- name    : AvramDividend.Classical.avram_f6_original_finitecap_admissible_upperstrip_expected_zero
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-18T17:23:26.553303+00:00
-- url     : https://prove2.me/theorems/cb1a7c38-88ad-4ae1-a420-677b7a6e9ea9
-- title:
--   Automatic original finite-cap upper strip occupation expected vanishing under admissibility
-- statement:
--   For the original spectrally negative unbounded-variation controlled Lévy process, positive finite cap C, original admissible strategy D and initial x within C, the expected time the physical reserve spends in the shrinking cap strip (C.toReal*(j+1)/(j+2), C.toReal] during [0,n] tends to zero. Removes the extra arbitrary real-valued reserve cap assumption from the existing Proved strip occupation lemma by deriving it from authentic IsAdmissibleLe and finite ENNReal C; directly helps finitecap Gaussian HJB upper strip error control.
-- source:
--   Proved admissibleLe_riskProcess_le_cap_all_times c521fe8f and Proved avram_gfinite64_original_global_cap_strip_expected_zero 9168b6b5.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_f6_original_finitecap_admissible_upperstrip_expected_zero
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hBV : ¬ X.BoundedVariation)
    (x : ℝ) (C : ℝ≥0∞) (hC : 0 < C) (hFinite : C ≠ ⊤)
    (hxc : ENNReal.ofReal x ≤ C)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (n : ℕ) (hn : 0 < n) :
    Tendsto
      (fun j : ℕ => ∫ ω, ∫ t in Ioo (0 : ℝ) (n : ℝ),
        if C.toReal * (((j + 1 : ℕ) : ℝ) / ((j + 2 : ℕ) : ℝ)) <
            riskProcess X x D (Real.toNNReal t) ω
        then (1 : ℝ) else 0 ∂volume ∂P)
      atTop (𝓝 (0 : ℝ)) := by sorry
