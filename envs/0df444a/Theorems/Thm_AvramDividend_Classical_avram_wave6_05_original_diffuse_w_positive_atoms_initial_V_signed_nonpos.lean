-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave6_05_original_diffuse_w_positive_atoms_initial_V_signed_nonpos
-- name    : AvramDividend.Classical.avram_wave6_05_original_diffuse_w_positive_atoms_initial_V_signed_nonpos
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-01T19:57:58.648101+00:00
-- url     : https://prove2.me/theorems/78629595-1fa4-4816-9ada-11ec47781806
-- title:
--   Actual stopped diffuse full Stieltjes dividend plus all positive right jumps and unrestricted time-zero caplinear payment signed nonpositive
-- statement:
--   For any actual capped admissible left-continuous finite-variation dividend strategy and any atomless dividend component (including singular-continuous variation), the ruin-stopped discounted diffuse derivative correction with ν-a.e interior gradient is nonpositive together with any summable countable series of all strictly positive pre-ruin w jump corrections and the unrestricted initial V caplinear correction. Crucially no initial capital cap hxc is imposed; the time-zero atom uses V because IsAdmissibleLe caps the true reserve only at t>0. This is the dividend sign interface for the genuine original-source controlled Ito–Meyer formula, with the original ruin paymentTimes convention; it does not claim generator or martingale identities.
-- source:
--   Reuse accepted positive countable w right-payment sign bf18b23c, accepted alltime caplinear initial atom sign 1a3ddaf1, and the same null-singleton a.e-localisation/integral_nonpos_of_ae proof pattern as accepted a9565727. Keep real IntegrableOn and Summable premises.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave6_05_original_positive_countable_w_right_payment_correction_nonpos
import Theorems.Thm_AvramDividend_Classical_avram_wave6_05_actual_alltime_caplinear_dividend_jump_drop

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal BigOperators

theorem AvramDividend.Classical.avram_wave6_05_original_diffuse_w_positive_atoms_initial_V_signed_nonpos
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (C : ℝ≥0∞) (hC : 0 < C)
    (q : ℝ) (w V : ℝ → ℝ)
    (hw_cont : ContinuousOn w (Ici 0))
    (hw_smooth : ContDiffOn ℝ 1 w
      {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (hw_grad : ∀ y : ℝ, 0 < y →
      ENNReal.ofReal y < C → 1 ≤ deriv w y)
    (hVtop : C = ⊤ → ∀ y : ℝ, V y = w y)
    (hVfinite : C ≠ ⊤ → ∀ y : ℝ,
      V y = if y ≤ C.toReal then w y
        else w C.toReal + (y - C.toReal))
    (D : ℝ≥0 → Ω → ℝ)
    (hD : IsAdmissibleLe X x C D)
    (ω : Ω) (T : ℝ≥0)
    (ν : Measure ℝ) [NullSingletonClass ν]
    (A : Set ℝ≥0) (hCount : A.Countable)
    (hA : ∀ t : A, 0 < (t : ℝ≥0) ∧
      ((t : ℝ≥0) : ℝ≥0∞) < ruinTime X x D ω)
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
    ((∫ s in paymentTimes (ruinTime X x D ω) ∩ Icc (0 : ℝ) (T : ℝ),
      Real.exp (-q * s) *
        (1 - deriv w (riskProcess X x D s.toNNReal ω)) ∂ν) +
    (∑' t : A, Real.exp (-(q * ((t : ℝ≥0) : ℝ))) *
      ((rightLimit D (t : ℝ≥0) ω - D (t : ℝ≥0) ω) +
        w (riskProcess X x D (t : ℝ≥0) ω -
          (rightLimit D (t : ℝ≥0) ω - D (t : ℝ≥0) ω)) -
        w (riskProcess X x D (t : ℝ≥0) ω)))) +
    ((rightLimit D 0 ω - D 0 ω) +
      V (riskProcess X x D 0 ω -
        (rightLimit D 0 ω - D 0 ω)) -
      V (riskProcess X x D 0 ω)) ≤ 0 := by sorry
