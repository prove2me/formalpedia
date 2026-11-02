-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave5_03_canonical_hjump_discounted_drift_full_stieltjes_hjb_budget
-- name    : AvramDividend.Classical.avram_wave5_03_canonical_hjump_discounted_drift_full_stieltjes_hjb_budget
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-01T09:59:11.609288+00:00
-- url     : https://prove2.me/theorems/70367a88-dd3d-4598-b95a-faa6d0a33890
-- title:
--   Both canonical stochastic cores' exact hjump hypotheses imply source stopped HJB drift plus full real Stieltjes correction budget without positive cap
-- statement:
--   Using the same original Lévy-controlled source, predictable true ruin stopped finite clock, generator HJB supersolution and exact right-jump hjump already supplied as assumptions to both BV and corrected UBV canonical cores, prove the combined generator drift integral plus full signed source real Stieltjes diffuse and eligible atomic correction is nonpositive. No positive-cap hC>0, BV/UBV smoothness, nonnegative w off path, new martingale or hypothetical chain rule is demanded beyond the canonical input. Diffuse signed integral retains its explicit paid-window ν-a.e interior support and real integrability/summability; therefore it also applies to the corrected UBV C=0 case when the diffuse restriction premise is discharged.
-- source:
--   Avram, Palmowski and Pistorius (2007) Proposition 4(i) deterministic finite-variation budget; imports Proved a6c40351 true stopped generator residual and canonical-hjump real Stieltjes nonpositivity. Relevant directly to BV ef7e6c20 and UBV 429e17ca.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave5_03_actual_discounted_ruin_clock_generator_residual_nonpos
import Theorems.Thm_AvramDividend_Classical_avram_wave5_03_canonical_hjump_ae_diffuse_full_stieltjes_control_nonpos

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical
noncomputable section

/-- Same original Lévy source and admissible dividends: the entire discounted
generator-plus-full-Stieltjes HJB finite-variation residual is nonpositive.
This contains no assumed stochastic Itô identity or martingale driver. -/

theorem AvramDividend.Classical.avram_wave5_03_canonical_hjump_discounted_drift_full_stieltjes_hjb_budget
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
    (q : ℝ) (hq : 0 ≤ q) (T : ℝ≥0)
    (hw_gen : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C →
      X.GeneratorIntegrable w y ∧ X.generator w y - q * w y ≤ 0)
    (μ : @Measure (ℝ≥0 × Ω) (𝓕.rightCont.predictable))
    (E : Set (ℝ≥0 × Ω))
    (hE : MeasurableSet[𝓕.rightCont.predictable] E)
    (hregion : ∀ p ∈ E,
      0 < Function.leftLim
        (fun s : ℝ≥0 => x + X.X s p.2 - rightLimit D s p.2) p.1 ∧
      ENNReal.ofReal (Function.leftLim
        (fun s : ℝ≥0 => x + X.X s p.2 - rightLimit D s p.2) p.1) < C)
    (hIntGen : IntegrableOn
      (fun p : ℝ≥0 × Ω =>
        (if p.1 ≤ T then
          Real.exp (-(q * (p.1 : ℝ))) *
            (if (p.1 : ℝ≥0∞) ≤ ruinTime X x D p.2 then (1 : ℝ) else 0)
         else 0) *
        (X.generator w (Function.leftLim
          (fun s : ℝ≥0 => x + X.X s p.2 - rightLimit D s p.2) p.1) -
          q * w (Function.leftLim
            (fun s : ℝ≥0 => x + X.X s p.2 - rightLimit D s p.2) p.1)))
      E μ)
    (ω : Ω)
    (ν : Measure ℝ) [NullSingletonClass ν]
    (J : Set ℝ≥0) (hJ : J.Countable)
    (hJT : ∀ t : J, (t : ℝ≥0) ≤ T)
    (hJP : ∀ t : J, ((t : ℝ≥0) : ℝ) ∈ paymentTimes (ruinTime X x D ω))
    (hlocAe : ∀ᵐ s ∂ν.restrict
        (paymentTimes (ruinTime X x D ω) ∩ Icc (0 : ℝ) (T : ℝ)),
      0 < riskProcess X x D s.toNNReal ω ∧
        ENNReal.ofReal (riskProcess X x D s.toNNReal ω) < C)
    (hIntDiv : IntegrableOn
      (fun s : ℝ => Real.exp (-q * s) *
        (1 - deriv w (riskProcess X x D s.toNNReal ω)))
      (paymentTimes (ruinTime X x D ω) ∩ Icc (0 : ℝ) (T : ℝ)) ν)
    (hSummable : Summable (fun t : J =>
      Real.exp (-(q * ((t : ℝ≥0) : ℝ))) *
        ((rightLimit D (t : ℝ≥0) ω - D (t : ℝ≥0) ω) +
          w (riskProcess X x D (t : ℝ≥0) ω -
            (rightLimit D (t : ℝ≥0) ω - D (t : ℝ≥0) ω)) -
          w (riskProcess X x D (t : ℝ≥0) ω)))) :
    (∫ p in E,
      (if p.1 ≤ T then
        Real.exp (-(q * (p.1 : ℝ))) *
          (if (p.1 : ℝ≥0∞) ≤ ruinTime X x D p.2 then (1 : ℝ) else 0)
       else 0) *
      (X.generator w (Function.leftLim
        (fun s : ℝ≥0 => x + X.X s p.2 - rightLimit D s p.2) p.1) -
        q * w (Function.leftLim
          (fun s : ℝ≥0 => x + X.X s p.2 - rightLimit D s p.2) p.1)) ∂μ) +
    ((∫ s in paymentTimes (ruinTime X x D ω) ∩ Icc (0 : ℝ) (T : ℝ),
      Real.exp (-q * s) *
        (1 - deriv w (riskProcess X x D s.toNNReal ω)) ∂ν) +
    (∑' t : J,
      Real.exp (-(q * ((t : ℝ≥0) : ℝ))) *
        ((rightLimit D (t : ℝ≥0) ω - D (t : ℝ≥0) ω) +
          w (riskProcess X x D (t : ℝ≥0) ω -
            (rightLimit D (t : ℝ≥0) ω - D (t : ℝ≥0) ω)) -
          w (riskProcess X x D (t : ℝ≥0) ω)))) ≤ 0 := by sorry
