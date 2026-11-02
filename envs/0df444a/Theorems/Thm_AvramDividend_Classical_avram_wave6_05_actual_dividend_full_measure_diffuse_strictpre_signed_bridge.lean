-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave6_05_actual_dividend_full_measure_diffuse_strictpre_signed_bridge
-- name    : AvramDividend.Classical.avram_wave6_05_actual_dividend_full_measure_diffuse_strictpre_signed_bridge
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-01T20:49:50.651383+00:00
-- url     : https://prove2.me/theorems/51782257-8580-4ca5-9cdf-9e6066e1a7c4
-- title:
--   Genuine original dividend Stieltjes atomic/atomless witness and discounted strict-prejump diffuse gradient signed domination
-- statement:
--   For every actual admissible dividend control of the original spectrally negative Lévy process, the genuine closed-horizon dividendMeasure splits into the exact countably right-atomic measure and an atomless complement. All atoms equal the true rightLimit D(t)-D(t), including the time-zero and horizon-end atoms; the discounted ENNReal integral splits into exactly the atomic and diffuse integrals without dropping continuous or singular-continuous mass. For the same actual atomless witness, if the derivative of w at the genuine strict original source-prejump controlled reserve x+leftLim X(t)-rightLimit D(t) is at least one almost everywhere on the ruin-stopped payment window, then the corresponding discounted signed real diffuse correction is nonpositive. The result imposes no regularity or finite-jump restriction on D, and no cap or w(0) assumption. It is the source-faithful actual-measure interface for the controlled Ito-Meyer finite-variation term, leaving countable jumps to the already Proved chronological secant results and generator/martingales to Chat 06.
-- source:
--   The canonical Proved actual original dividend Stieltjes decomposition with strict-prejump gradient equality provides the source exact μatom and μdiffuse witnesses; lintegral_add_measure gives the complete weighted budget, and integral_nonpos_of_ae with Real.exp_pos gives the diffuse signed inequality.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave4_04b_actual_dividend_diffuse_derivative_prejump_stieltjes_integral_eq

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal BigOperators

theorem AvramDividend.Classical.avram_wave6_05_actual_dividend_full_measure_diffuse_strictpre_signed_bridge
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (x : ℝ)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissible X x D)
    (ω : Ω) (T : ℝ≥0) :
    let μ : Measure ℝ :=
      (dividendMeasure D ω).restrict (Icc (0 : ℝ) (T : ℝ))
    ∃ (A : Set ℝ) (μatom μdiffuse : Measure ℝ),
      A.Countable ∧ MeasurableSet A ∧
      μ = μatom + μdiffuse ∧
      μatom = Measure.sum (fun t : A => μ {(t : ℝ)} • Measure.dirac (t : ℝ)) ∧
      μatom Aᶜ = 0 ∧ NullSingletonClass μdiffuse ∧
      (∀ t : ℝ≥0, t ≤ T →
        μ {(t : ℝ)} =
          ENNReal.ofReal (rightLimit D t ω - D t ω)) ∧
      (∀ (q : ℝ) (w : ℝ → ℝ),
        (∫⁻ s, ENNReal.ofReal (Real.exp (-(q * s))) ∂μ) =
          (∫⁻ s, ENNReal.ofReal (Real.exp (-(q * s))) ∂μatom) +
          (∫⁻ s, ENNReal.ofReal (Real.exp (-(q * s))) ∂μdiffuse) ∧
        ((∀ᵐ s ∂μdiffuse.restrict
            (paymentTimes (ruinTime X x D ω) ∩ Icc (0 : ℝ) (T : ℝ)),
          1 ≤ deriv w (x +
            Function.leftLim (fun r : ℝ≥0 => X.X r ω) s.toNNReal -
            rightLimit D s.toNNReal ω)) →
          (∫ s in paymentTimes (ruinTime X x D ω) ∩ Icc (0 : ℝ) (T : ℝ),
            Real.exp (-(q * s)) *
              (1 - deriv w (x +
                Function.leftLim (fun r : ℝ≥0 => X.X r ω) s.toNNReal -
                rightLimit D s.toNNReal ω)) ∂μdiffuse) ≤ 0)) := by sorry
