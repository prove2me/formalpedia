-- Prove2me | Theorems.Thm_AvramDividend_Classical_gaussian_esscher_C1_derivative_resolvent_of_positive_sigma
-- name    : AvramDividend.Classical.gaussian_esscher_C1_derivative_resolvent_of_positive_sigma
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-24T08:27:19.689932+00:00
-- url     : https://prove2.me/theorems/fae6fb1b-782b-4acb-bb01-5a004bff323e
-- title:
--   Gaussian Esscher integrated Volterra equation admits a C1 derivative resolvent
-- statement:
--   For a positive Gaussian Lévy coefficient and positive Esscher root ψ(φ)=q, the Esscher-tilted q-scale V satisfies an integrated Volterra equation with positive coefficient a and integrable native Gaussian Lévy kernel K. Establish that the same equation has a derivative resolvent g, continuous on nonnegative time, C1 on positive time, satisfying a g + (β+K)*g=1. The existence of a merely continuous g and the native kernel's positive-time continuity, nonnegativity and antitonicity have already been Proved. The missing genuinely analytic step is C1 smoothness of g despite the kernel's possible integrable singularity at zero. This theorem is the exact next dependency for Gaussian C2 scale smoothness without Standing.

import Mathlib.Analysis.Calculus.ContDiff.Defs
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Theorems.Thm_AvramDividend_Classical_gaussian_esscher_volterra_kernel_equation_of_positive_sigma
import Theorems.Thm_AvramDividend_Classical_causal_volterra_l1_derivative_resolvent_exists
open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

theorem AvramDividend.Classical.gaussian_esscher_C1_derivative_resolvent_of_positive_sigma
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {ℱ : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P ℱ)
    (q : ℝ) (hq : 0 < q)
    (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (hσ : 0 < X.σ)
    (φ : ℝ) (hφ : 0 < φ) (hroot : X.ψ φ = q)
    (V : ℝ → ℝ)
    (hV : ∀ x : ℝ, 0 < x →
      V x = Real.exp (-(φ * x)) * W x) :
    ∃ (a β : ℝ) (K g : ℝ → ℝ),
      0 < a ∧
      IntegrableOn K (Ioi (0 : ℝ)) volume ∧
      ContinuousOn g (Ici (0 : ℝ)) ∧
      ContDiffOn ℝ 1 g (Ioi (0 : ℝ)) ∧
      (∀ x : ℝ, 0 < x →
        a * V x +
          (∫ s in Ioc (0 : ℝ) x,
            (β + K (x - s)) * V s ∂volume) = x) ∧
      (∀ x : ℝ, 0 < x →
        a * g x +
          (∫ s in Ioc (0 : ℝ) x,
            (β + K (x - s)) * g s ∂volume) = 1) := by sorry
