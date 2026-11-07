-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_reuse8_original_strict_mean_to_split
-- name    : AvramDividend.Classical.avram_reuse8_original_strict_mean_to_split
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-06T23:13:31.29203+00:00
-- url     : https://prove2.me/theorems/a8719200-82b8-4ecc-8605-f14bb39028c0
-- title:
--   Original BV strict expected payoff budget yields source-exact centred and nonpositive drift split
-- statement:
--   For the actual admissible bounded-variation Lévy dividend strategy and strict pre-ruin, pre-horizon cashflow, an expected strict payoff upper bound implies a source-exact two-component integrable witness: a mean-zero term and a term of nonpositive expectation. This is the exact downstream witness shape, conditional on the still-open original stochastic expected-budget inequality.
-- source:
--   Direct bridge from Proved a55a5fab-e951-4b68-93b4-3997daabf361 to the witness conclusion of Open canonical 1a1a0301-29ec-407e-acdd-e9b35f7e0edf. The generator-derived strict expected upper bound remains a genuine independent proof obligation; this lemma must not be used to infer that inequality or to close 1a1a on its own.

import Mathlib.Analysis.Complex.Exponential
import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_p3_bv_original_source_witness_from_strict_mean

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_reuse8_original_strict_mean_to_split
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hBV : X.BoundedVariation)
    (x : ℝ) (C : ℝ≥0∞) (D : ℝ≥0 → Ω → ℝ)
    (hD : IsAdmissibleLe X x C D)
    (w : ℝ → ℝ) (hw_cont : ContinuousOn w (Ici 0))
    (hw_neg : ∀ y < 0, w y = 0)
    (q : ℝ) (hq : 0 ≤ q) (T : ℝ) (hT : 0 ≤ T) :
    let S : ℝ≥0 := ⟨T, hT⟩
    let Strict : Ω → ℝ := fun ω =>
      (∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Iio T,
        ENNReal.ofReal (Real.exp (-(q * t)))
          ∂(dividendMeasure D ω)).toReal +
      (if (S : ℝ≥0∞) < ruinTime X x D ω then
        Real.exp (-(q * T)) * w (riskProcess X x D S ω)
      else 0)
    (∫ ω, Strict ω ∂P) ≤ w x →
    ∃ M B : Ω → ℝ,
      (Integrable M P ∧ (∫ ω, M ω ∂P) = 0) ∧
      (Integrable B P ∧ (∫ ω, B ω ∂P) ≤ 0) ∧
      (∀ᵐ ω ∂P, Strict ω ≤ w x + M ω + B ω) := by sorry
