-- Prove2me | Theorems.Thm_CohnElkies_antiFourierWitness_capped_poisson_majorization_of_real_extension
-- name    : CohnElkies.antiFourierWitness_capped_poisson_majorization_of_real_extension
-- status  : Open
-- author  : @marwahaha
-- created : 2026-10-19T10:57:01.402116+00:00
-- url     : https://prove2.me/theorems/cd276aac-ad08-427a-8c35-273e1bc6d23a
-- title:
--   CohnElkies.antiFourierWitness_capped_poisson_majorization_of_real_extension
-- source:
--   https://github.com/openai/ten-proofs/tree/94bc0feb6a9ff12c7d31d6de640a725c9d43d2b6 | SpherePacking | external Lean 4.33.1 validation; bundle SHA256 ecca43e9570778e44777003bd5984d4ec94cd395fce5324c69b88ac50ad79ed2

import Mathlib
import Definitions.Def_SpherePacking
set_option autoImplicit true
open CohnElkies
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 800000
noncomputable section
open Asymptotics Bornology Complex Filter Function MeasureTheory Metric Set
open scoped Filter FourierTransform Real SchwartzMap Topology

theorem CohnElkies.antiFourierWitness_capped_poisson_majorization_of_real_extension
    {d : ℕ} (hd : 0 < d) {R : ℝ}
    (w : AntiFourierWitness d R) (D : ℝ)
    (E : ℂ → ℝ)
    (hE : ContinuousOn E
      (Complex.im ⁻¹'
        Icc (-((d : ℝ) / 2)) ((d : ℝ) / 2)))
    (hEinterior : ∀ z : ℂ,
      z.im ∈ Ioo (-((d : ℝ) / 2)) ((d : ℝ) / 2) →
        E z = (lowerStripCappedGammaOuter
          ((d : ℝ) / 2) R D z).re)
    (hEbottom : ∀ z : ℂ,
      z.im = -((d : ℝ) / 2) →
        E z = lowerGammaBoundaryCapped
          ((d : ℝ) / 2) R D z.re)
    (hEtop : ∀ z : ℂ,
      z.im = (d : ℝ) / 2 → E z = 0)
    (hcap : ∀ y : ℝ,
      ‖normalizedRadialMellinStrip hd w.function R
        ((y : ℂ) -
          Complex.I * (((d : ℝ) / 2 : ℝ) : ℂ))‖ ≤
        Real.exp (lowerGammaBoundaryCapped
          ((d : ℝ) / 2) R D y))
    {σ : ℝ} (hbelow : -1 < σ) (habove : σ < 1)
    (s : ℝ) :
    ‖normalizedRadialMellinStrip hd w.function R
      ((s : ℂ) + Complex.I *
        ((σ * ((d : ℝ) / 2) : ℝ) : ℂ))‖ ≤
      Real.exp
        (∫ T : ℝ, stripPoissonKernel σ T *
          lowerGammaBoundaryCapped
            ((d : ℝ) / 2) R D
            (s - ((d : ℝ) / 2) * T)) := by sorry
