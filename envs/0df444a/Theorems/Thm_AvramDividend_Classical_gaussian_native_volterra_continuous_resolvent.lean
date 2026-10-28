-- Prove2me | Theorems.Thm_AvramDividend_Classical_gaussian_native_volterra_continuous_resolvent
-- name    : AvramDividend.Classical.gaussian_native_volterra_continuous_resolvent
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-24T15:13:31.437736+00:00
-- url     : https://prove2.me/theorems/83478efb-faeb-4bef-829d-65c7a3413095
-- title:
--   Native monotone Gaussian Volterra kernel with continuous derivative resolvent
-- statement:
--   For the actual q-scale function and Gaussian Esscher root, select the canonical native double-tail kernel, whose positive-time continuity, nonnegativity and antitonicity are guaranteed by the Lévy hypotheses, and construct its continuous causal derivative resolvent g. The same kernel and coefficients satisfy the exact tilted-scale Volterra equation. This reduces the Open Gaussian C1 derivative-resolvent theorem to the regularity step ContDiffOn ℝ 1 g (Ioi 0) for this particular nonnegative antitone integrable kernel.
-- source:
--   Compose the Proved canonical Gaussian Esscher Volterra identity, native double-tail integrability/positive-time regularity, and continuous L1 Volterra derivative-resolvent existence.

import Mathlib.Analysis.Complex.Exponential
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Theorems.Thm_AvramDividend_Classical_gaussian_native_double_tail_kernel_full_regularity
import Theorems.Thm_AvramDividend_Classical_gaussian_native_levy_esscher_double_tail_integrable
import Theorems.Thm_AvramDividend_Classical_gaussian_esscher_canonical_volterra_identity_of_positive_sigma
import Theorems.Thm_AvramDividend_Classical_causal_volterra_l1_derivative_resolvent_exists
open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

theorem AvramDividend.Classical.gaussian_native_volterra_continuous_resolvent
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
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
      ContinuousOn K (Ioi (0 : ℝ)) ∧
      AntitoneOn K (Ioi (0 : ℝ)) ∧
      (∀ t : ℝ, 0 < t → 0 ≤ K t) ∧
      ContinuousOn g (Ici (0 : ℝ)) ∧
      (∀ x : ℝ, 0 < x →
        a * V x +
          (∫ s in Ioc (0 : ℝ) x,
            (β + K (x - s)) * V s ∂volume) = x) ∧
      (∀ x : ℝ, 0 < x →
        a * g x +
          (∫ s in Ioc (0 : ℝ) x,
            (β + K (x - s)) * g s ∂volume) = 1) := by sorry
