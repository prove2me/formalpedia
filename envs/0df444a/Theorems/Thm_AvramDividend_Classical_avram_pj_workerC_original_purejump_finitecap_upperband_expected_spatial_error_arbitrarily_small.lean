-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_pj_workerC_original_purejump_finitecap_upperband_expected_spatial_error_arbitrarily_small
-- name    : AvramDividend.Classical.avram_pj_workerC_original_purejump_finitecap_upperband_expected_spatial_error_arbitrarily_small
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-19T12:36:29.119607+00:00
-- url     : https://prove2.me/theorems/5ab44803-a213-437d-a625-a3948c12975e
-- title:
--   Original infinite-variation finite-cap dividend reserve admits arbitrarily small expected physical upper-contact band occupation, with an explicit natural-number truncation
-- statement:
--   For the actual original infinite-variation spectrally negative Levy process and its original admissible post-right dividend strategy with finite cap C, choose an increasing finitecap upperstrip truncation j so that the expected physical time occupation of the band {risk reserve> C*(j+1)/(j+2)} on the original finite horizon [0,n] is at most any epsilon>0. The estimate is the original expectation over time and sample, derived from source Proved stochastic occupation, not a hypothetical process. It provides quantitative spatial localisation K control at the finite-cap boundary.
-- source:
--   Proved cb1a7c38 actual original finitecap admissible upperstrip expected zero under unbounded variation.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_f6_original_finitecap_admissible_upperstrip_expected_zero
open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_pj_workerC_original_purejump_finitecap_upperband_expected_spatial_error_arbitrarily_small
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hBV : ¬ X.BoundedVariation)
    (x : ℝ) (C : ℝ≥0∞) (hC : 0 < C) (hFinite : C ≠ ⊤)
    (hxc : ENNReal.ofReal x ≤ C)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (n : ℕ) (hn : 0 < n) :
    ∀ ε : ℝ, 0 < ε → ∃ j : ℕ,
      ∫ ω, ∫ t in Ioo (0 : ℝ) (n : ℝ),
        if C.toReal * (((j + 1 : ℕ) : ℝ) / ((j + 2 : ℕ) : ℝ)) <
            riskProcess X x D (Real.toNNReal t) ω
        then (1 : ℝ) else 0 ∂volume ∂P ≤ ε := by sorry
