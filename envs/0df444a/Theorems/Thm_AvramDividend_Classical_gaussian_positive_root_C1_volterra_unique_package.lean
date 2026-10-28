-- Prove2me | Theorems.Thm_AvramDividend_Classical_gaussian_positive_root_C1_volterra_unique_package
-- name    : AvramDividend.Classical.gaussian_positive_root_C1_volterra_unique_package
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-24T08:21:10.350017+00:00
-- url     : https://prove2.me/theorems/b62cf764-f44f-4fa2-8560-a3c58cd7d91d
-- title:
--   Gaussian q-scale function admits a positive Esscher root and unique C1 Volterra representation
-- statement:
--   For every spectrally negative Lévy process with positive Gaussian coefficient, every q>0 and its canonical q-scale function W, construct an Esscher exponent φ>0 with ψ(φ)=q. The damped scale V(x)=e^{−φx}W(x) is C1 on (0,∞) and uniquely solves a real, integrated causal Volterra equation with positive leading coefficient and integrable jump kernel, among all continuous locally bounded solutions. Combine the already Proved positive Gaussian Esscher root, Gaussian Volterra uniqueness and C1 regularity; requires no Standing assumptions or separately supplied Esscher root. This gives a hypothesis-minimal entrypoint for the Gaussian C2 smoothing project.

import Mathlib.Analysis.Calculus.ContDiff.Defs
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Theorems.Thm_AvramDividend_Classical_positive_esscher_root_of_gaussian
import Theorems.Thm_AvramDividend_Classical_gaussian_esscher_volterra_C1_unique
open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

theorem AvramDividend.Classical.gaussian_positive_root_C1_volterra_unique_package
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {ℱ : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P ℱ)
    (q : ℝ) (hq : 0 < q)
    (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (hσ : 0 < X.σ) :
    ∃ φ : ℝ, 0 < φ ∧ X.ψ φ = q ∧
      ContDiffOn ℝ 1 (fun x : ℝ => Real.exp (-(φ * x)) * W x) (Ioi (0 : ℝ)) ∧
      ∃ (a β : ℝ) (K : ℝ → ℝ),
        0 < a ∧ IntegrableOn K (Ioi (0 : ℝ)) volume ∧
        (∀ x : ℝ, 0 < x →
          a * (fun x : ℝ => Real.exp (-(φ * x)) * W x) x +
            (∫ s in Ioc (0 : ℝ) x,
              (β + K (x - s)) * (fun x : ℝ => Real.exp (-(φ * x)) * W x) s ∂volume) = x) ∧
        (∀ G : ℝ → ℝ,
          ContinuousOn G (Ioi (0 : ℝ)) →
          (∀ R : ℝ, 0 < R →
            ∃ C : ℝ, ∀ x : ℝ, x ∈ Ioc (0 : ℝ) R → |G x| ≤ C) →
          (∀ x : ℝ, 0 < x →
            a * G x +
              (∫ s in Ioc (0 : ℝ) x,
                (β + K (x - s)) * G s ∂volume) = x) →
          ∀ x : ℝ, 0 < x → G x = (fun x : ℝ => Real.exp (-(φ * x)) * W x) x) := by sorry
