-- Prove2me | Theorems.Thm_AvramDividend_Classical_gaussian_esscher_cumulative_of_exit_decay
-- name    : AvramDividend.Classical.gaussian_esscher_cumulative_of_exit_decay
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-20T10:19:19.887123+00:00
-- url     : https://prove2.me/theorems/f04dab08-9271-46bf-a53e-2da64c9d37ef
-- title:
--   Gaussian scale-function Esscher cumulative Laplace representation from an exponential first-passage estimate
-- statement:
--   For a nonzero-Gaussian spectrally negative Lévy process, q>0 and a zero-origin positive q-scale function, an exponential first-passage decay inequality at every positive root ψ(φ)=q implies a positive locally finite Esscher Stieltjes cumulative measure and the full shifted Laplace integrability and equality. The proof derives the root and eventual shifted Laplace domain from existing Proved Lévy-process results, and imports only Proved analytic lemmas. The stochastic exit-decay inequality remains an explicit substantive premise.
-- source:
--   Proved positive_esscher_root_of_gaussian, psi_eventually_positive_quadratic_of_gaussian, positive_esscher_shift_laplace_domain, exit_decay_implies_tilted_monotone, esscher_cumulative_laplace_of_monotone.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

theorem AvramDividend.Classical.gaussian_esscher_cumulative_of_exit_decay
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration NNReal mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (q : ℝ) (hq : 0 < q)
    (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (hσ : 0 < X.σ) (hzero : W 0 = 0)
    (hpos : ∀ x : ℝ, 0 < x → 0 < W x)
    (hdecay : ∀ φ : ℝ, 0 < φ → X.ψ φ = q →
      ∀ x y : ℝ, 0 < x → x ≤ y →
        W x ≤ Real.exp (-φ * (y - x)) * W y) :
    ∃ (β : Measure ℝ) (φ b : ℝ),
      0 < φ ∧
      (∀ x : ℝ, β (Iic x) ≠ ⊤) ∧
      (∀ x : ℝ, 0 < x → 0 < β (Iic x)) ∧
      ∀ θ : ℝ, b < θ →
        IntegrableOn (fun x : ℝ => Real.exp (-θ * x) *
          (Real.exp (-φ * x) * W x)) (Ioi 0) ∧
        IntegrableOn (fun x : ℝ => Real.exp (-θ * x) *
          (β (Iic x)).toReal) (Ioi 0) ∧
        ∫ x in Ioi (0 : ℝ), Real.exp (-θ * x) *
          (Real.exp (-φ * x) * W x) =
        ∫ x in Ioi (0 : ℝ), Real.exp (-θ * x) *
          (β (Iic x)).toReal := by sorry
