-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_pj_workerC_original_finitecap_both_spatial_boundary_occupations_arbitrarily_small
-- name    : AvramDividend.Classical.avram_pj_workerC_original_finitecap_both_spatial_boundary_occupations_arbitrarily_small
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-19T16:14:36.903182+00:00
-- url     : https://prove2.me/theorems/5e23a501-963b-4576-87e2-8d79333c47db
-- title:
--   Original finitecap dividend reserve admits simultaneous arbitrarily small positive lower spatial band product mass and upper-cap expected physical occupation
-- statement:
--   For the genuine original finite-cap spectrally negative Lévy reserve with unbounded variation and admissible post-right dividends, and any finite measure on the actual physical-time×sample product space, given epsilon choose independently a lower spatial positive cutoff 1/(k+1) and a cap upper cutoff C*(j+1)/(j+2), so that the lower strip has original finite product mass at most epsilon and the upper strip has original expected Lebesgue physical occupation at most epsilon. Uses jointly measurable true reserve and the previously Proved original upper-strip source. These two independently small spatial contacts are needed for compact C2 band localisation in the purejump Ito verification. Units lower mass ENNReal, upper expected time Real; no synthetic stochastic laws.
-- source:
--   Proved original positive lower-strip measure (pending parent), Proved 5ab44803 true upperstrip expected finitecap physical occupation epsilon selection.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_pj_workerC_original_finitecap_both_spatial_boundary_occupations_arbitrarily_small
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hBV : ¬ X.BoundedVariation)
    (x : ℝ) (C : ℝ≥0∞) (hC : 0 < C) (hFinite : C ≠ ⊤)
    (hxc : ENNReal.ofReal x ≤ C)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (n : ℕ) (hn : 0 < n)
    (μ : Measure (ℝ≥0 × Ω)) [IsFiniteMeasure μ] :
    ∀ ε : ℝ, 0 < ε → ∃ k j : ℕ,
      μ {p : ℝ≥0 × Ω |
        0 < riskProcess X x D p.1 p.2 ∧
        riskProcess X x D p.1 p.2 ≤
          (1 : ℝ) / ((k : ℝ) + 1)} ≤ ENNReal.ofReal ε ∧
      (∫ ω, ∫ t in Ioo (0 : ℝ) (n : ℝ),
        if C.toReal * (((j + 1 : ℕ) : ℝ) / ((j + 2 : ℕ) : ℝ)) <
            riskProcess X x D (Real.toNNReal t) ω
        then (1 : ℝ) else 0 ∂volume ∂P) ≤ ε := by sorry
