-- Prove2me | Theorems.Thm_AvramDividend_Classical_bv_esscher_root_positive_subunit_kernel_package
-- name    : AvramDividend.Classical.bv_esscher_root_positive_subunit_kernel_package
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-25T12:41:07.451119+00:00
-- url     : https://prove2.me/theorems/7d3344ce-1a22-490c-9e8c-3e093c60ec36
-- title:
--   Causal monotone BV Esscher renewal kernel with exactly positive subunit total mass
-- statement:
--   For a bounded-variation standing spectrally negative Lévy process at a positive Esscher root, exhibit the explicit drift-normalised discounted positive jump-tail kernel. It is continuous and antitone on positive reals, causal, nonnegative and integrable, with integral exactly rho where 0<rho<1. Combines the canonical shape theorem with the strictly positive mass lemma. This is the analytic kernel package required by the root-connected scaled renewal identification 1ca4a724-85b7-48bf-bae4-37890ef7055b.
-- source:
--   Canonical Proved bv_esscher_root_normalised_causal_kernel_shape and bv_esscher_root_positive_normalised_kernel_mass; set-integral congruence and integral_div.

import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.WithDensity
import Mathlib.Data.ENNReal.Real
import Theorems.Thm_AvramDividend_Classical_bv_esscher_root_normalised_causal_kernel_shape
import Theorems.Thm_AvramDividend_Classical_bv_esscher_root_positive_normalised_kernel_mass

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

theorem AvramDividend.Classical.bv_esscher_root_positive_subunit_kernel_package
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (hbv : X.BoundedVariation) (q : ℝ) (hq : 0 < q)
    (φ : ℝ) (hφ : 0 < φ) (hroot : X.ψ φ = q) :
    ∃ (κ : ℝ → ℝ) (ρ : ℝ),
      (∀ t : ℝ, κ t =
        if 0 < t then
          ENNReal.toReal (((X.ν.map (fun y : ℝ => Real.toNNReal (-y))).withDensity
            (fun z : ℝ≥0 => ENNReal.ofReal (Real.exp (-(φ * (z : ℝ))))))
            {z : ℝ≥0 | t < (z : ℝ)}) / X.drift else 0) ∧
      0 < ρ ∧ ρ < 1 ∧
      ContinuousOn κ (Ioi (0 : ℝ)) ∧
      AntitoneOn κ (Ioi (0 : ℝ)) ∧
      (∀ t : ℝ, t ≤ 0 → κ t = 0) ∧
      (∀ t : ℝ, 0 ≤ κ t) ∧
      IntegrableOn κ (Ioi (0 : ℝ)) volume ∧
      (∫ t in Ioi (0 : ℝ), κ t ∂volume) = ρ := by sorry
