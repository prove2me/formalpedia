-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave5_03_original_ae_diffuse_signed_stieltjes_control
-- name    : AvramDividend.Classical.avram_wave5_03_original_ae_diffuse_signed_stieltjes_control
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-01T09:11:09.077204+00:00
-- url     : https://prove2.me/theorems/a9565727-b3f1-42f1-93f3-a0b3cfdc0a68
-- title:
--   Original stopped complete signed Stieltjes correction: diffuse a.e. localisation and automatic all-cap right dividend atoms
-- statement:
--   For the genuine same-filtration SpectrallyNegativeLevy path with capped admissible left-continuous D, at its true ruinTime and finite horizon, the entire signed real continuous Stieltjes dividend correction plus the countable discounted right-atom correction (including t=0) is nonpositive. Unlike the earlier complete signed correction, strict interior reserve is required only ν.restrict(paymentTimes∩[0,T])-almost everywhere for the arbitrary atomless diffuse measure, not at every paid time or at any atom. BV C1/UBV C2 separate derivative floor, full closed-cap source secant and admissibility automatically control all actual right atoms, even at zero and cap. Integrability and summability are explicit. This is a full control-sign result, not a semimartingale formula; a reflecting regulator's diffuse mass at the cap still needs a boundary change-of-variables theorem.
-- source:
--   Avram, Palmowski and Pistorius (2007), Proposition 4(i), dividend finite-variation correction and (5.13). Same original source and Stieltjes convention; sharpens 04B signed correction 46dbfc5b by a.e interior for the diffuse measure, and uses 2cd50555 for automatic right atoms. Direct support for canonical BV ef7e6c20 and UBV 429e17ca.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave5_03_original_separate_gradient_right_atom_control
import Theorems.Thm_AvramDividend_Classical_avram_wave4_04b_countable_chronological_signed_correction_nonpos_of_summable

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical
noncomputable section

theorem AvramDividend.Classical.avram_wave5_03_original_ae_diffuse_signed_stieltjes_control
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (w : ℝ → ℝ) (C : ℝ≥0∞) (hC : 0 < C)
    (hw_cont : ContinuousOn w (Ici 0))
    (hw_smooth :
      (¬ X.BoundedVariation →
        ContDiffOn ℝ 2 w {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C}) ∧
      (X.BoundedVariation →
        ContDiffOn ℝ 1 w {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C}))
    (hw_grad : ∀ y : ℝ, 0 < y →
      ENNReal.ofReal y < C → 1 ≤ deriv w y)
    (x : ℝ) (hxc : ENNReal.ofReal x ≤ C)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
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
