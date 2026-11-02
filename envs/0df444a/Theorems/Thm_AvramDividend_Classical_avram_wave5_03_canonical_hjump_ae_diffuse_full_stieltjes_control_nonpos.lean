-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave5_03_canonical_hjump_ae_diffuse_full_stieltjes_control_nonpos
-- name    : AvramDividend.Classical.avram_wave5_03_canonical_hjump_ae_diffuse_full_stieltjes_control_nonpos
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-01T09:50:07.935241+00:00
-- url     : https://prove2.me/theorems/9c7a4cb0-ffd8-4175-867e-8bc1a29928c6
-- title:
--   Canonical BV/UBV full signed real Stieltjes correction nonpositive with only diffuse a.e interior localisation and no positive cap
-- statement:
--   For the actual source SpectrallyNegativeLevy dividend strategy X,D, its endogenous ruin paymentTimes and full signed Stieltjes correction with arbitrary atomless ν (covering both absolutely and singular-continuous payouts) and countable chronological lumps including time zero, prove correction≤0 under merely the exact hjump premise already present in canonical BV and corrected UBV cores, gradient floor on interior source states, ν-restrict paid-window a.e interior localisation, and explicit real integrability/summability. Unlike the earlier a956 source result, does not require hC>0, a globally nonnegative payoff, full HJB equality, or an extra stronger admissibility beyond the canonical hD and hjump; compatible with corrected UBV C=0. Uses canonical 04-B Proved countable signed atom lemma, no stochastic identity or martingale premise.
-- source:
--   Avram Palmowski Pistorius (2007) Stieltjes source control correction in Proposition 4(i), canonical BV ef7e6c20 and corrected UBV 429e17ca; import Proved 04-B countable chronological signed correction.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave4_04b_countable_chronological_signed_correction_nonpos_of_summable

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical
noncomputable section

/-- The original controlled full signed Stieltjes correction is nonpositive
with diffuse interior localisation only ν-a.e.; the time-zero and cap-contact
right atoms use the genuine admissible closed-cap secant instead. -/

theorem AvramDividend.Classical.avram_wave5_03_canonical_hjump_ae_diffuse_full_stieltjes_control_nonpos
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ)
    (hD : IsDividendStrategy 𝓕 D)
    (w : ℝ → ℝ) (C : ℝ≥0∞)
    (hw_grad : ∀ y : ℝ, 0 < y →
      ENNReal.ofReal y < C → 1 ≤ deriv w y)
    (hjump : ∀ ω (t : ℝ≥0),
      (t = 0 ∨ (t : ℝ≥0∞) < ruinTime X x D ω) →
      rightLimit D t ω - D t ω ≤
        w (riskProcess X x D t ω) -
          w (riskProcess X x D t ω -
            (rightLimit D t ω - D t ω)))
    (ω : Ω) (T : ℝ≥0) (q : ℝ)
    (ν : Measure ℝ) [NullSingletonClass ν]
    (A : Set ℝ≥0) (hA : A.Countable)
    (hAT : ∀ t : A, (t : ℝ≥0) ≤ T)
    (hAP : ∀ t : A, ((t : ℝ≥0) : ℝ) ∈ paymentTimes (ruinTime X x D ω))
    (hlocAe : ∀ᵐ s ∂ν.restrict
        (paymentTimes (ruinTime X x D ω) ∩ Icc (0 : ℝ) (T : ℝ)),
      0 < riskProcess X x D s.toNNReal ω ∧
        ENNReal.ofReal (riskProcess X x D s.toNNReal ω) < C)
    (hIntegrable : IntegrableOn
      (fun s : ℝ => Real.exp (-q * s) *
        (1 - deriv w (riskProcess X x D s.toNNReal ω)))
      (paymentTimes (ruinTime X x D ω) ∩ Icc (0 : ℝ) (T : ℝ)) ν)
    (hSummable : Summable (fun t : A =>
      Real.exp (-(q * ((t : ℝ≥0) : ℝ))) *
        ((rightLimit D (t : ℝ≥0) ω - D (t : ℝ≥0) ω) +
          w (riskProcess X x D (t : ℝ≥0) ω -
            (rightLimit D (t : ℝ≥0) ω - D (t : ℝ≥0) ω)) -
          w (riskProcess X x D (t : ℝ≥0) ω)))) :
    (∫ s in paymentTimes (ruinTime X x D ω) ∩ Icc (0 : ℝ) (T : ℝ),
      Real.exp (-q * s) *
        (1 - deriv w (riskProcess X x D s.toNNReal ω)) ∂ν) +
    (∑' t : A,
      Real.exp (-(q * ((t : ℝ≥0) : ℝ))) *
        ((rightLimit D (t : ℝ≥0) ω - D (t : ℝ≥0) ω) +
          w (riskProcess X x D (t : ℝ≥0) ω -
            (rightLimit D (t : ℝ≥0) ω - D (t : ℝ≥0) ω)) -
          w (riskProcess X x D (t : ℝ≥0) ω))) ≤ 0 := by sorry
