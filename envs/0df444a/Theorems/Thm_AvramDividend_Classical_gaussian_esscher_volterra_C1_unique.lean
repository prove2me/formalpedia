-- Prove2me | Theorems.Thm_AvramDividend_Classical_gaussian_esscher_volterra_C1_unique
-- name    : AvramDividend.Classical.gaussian_esscher_volterra_C1_unique
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-23T22:58:10.932776+00:00
-- url     : https://prove2.me/theorems/0946f02d-91c2-4e00-a88d-46fe8e64186c
-- title:
--   Gaussian Esscher tilted scale is the unique C1 solution of its canonical causal Volterra equation
-- statement:
--   For a positive Gaussian coefficient and any positive Esscher root ψ(φ)=q, let V(x)=e^(−φx) W^(q)(x) on positive reserves. The Gaussian scale-function continuity and local boundedness estimates and the canonical native Levy Volterra identity yield coefficients a>0, β and K∈L1(0,∞) such that V solves the integrated causal second-kind Volterra equation. Volterra smoothing makes V C1, and the Volterra uniqueness theorem shows that every other continuous locally bounded solution using these canonical coefficients agrees with V on the positive axis. No Standing assumptions or differentiability of the native Levy kernel are assumed. This packages the full remote-proved analytic bridge for Gaussian scale-function regularity.

import Mathlib.Analysis.Calculus.ContDiff.Defs
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Theorems.Thm_AvramDividend_Classical_gaussian_esscher_tilted_scale_continuous
import Theorems.Thm_AvramDividend_Classical_gaussian_esscher_tilted_scale_locally_bounded
import Theorems.Thm_AvramDividend_Classical_gaussian_esscher_volterra_kernel_equation_of_positive_sigma
import Theorems.Thm_AvramDividend_Classical_integrated_volterra_regularizes_C1
import Theorems.Thm_AvramDividend_Classical_causal_volterra_l1_continuous_solution_unique

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

theorem AvramDividend.Classical.gaussian_esscher_volterra_C1_unique
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
    ContDiffOn ℝ 1 V (Ioi (0 : ℝ)) ∧
    ∃ (a β : ℝ) (K : ℝ → ℝ),
      0 < a ∧
      IntegrableOn K (Ioi (0 : ℝ)) volume ∧
      (∀ x : ℝ, 0 < x →
        a * V x +
          (∫ s in Ioc (0 : ℝ) x,
            (β + K (x - s)) * V s ∂volume) = x) ∧
      (∀ G : ℝ → ℝ,
        ContinuousOn G (Ioi (0 : ℝ)) →
        (∀ R : ℝ, 0 < R →
          ∃ C : ℝ, ∀ x : ℝ, x ∈ Ioc (0 : ℝ) R → |G x| ≤ C) →
        (∀ x : ℝ, 0 < x →
          a * G x +
            (∫ s in Ioc (0 : ℝ) x,
              (β + K (x - s)) * G s ∂volume) = x) →
        ∀ x : ℝ, 0 < x → G x = V x) := by sorry
