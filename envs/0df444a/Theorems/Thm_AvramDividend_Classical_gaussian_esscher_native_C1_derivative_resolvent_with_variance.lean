-- Prove2me | Theorems.Thm_AvramDividend_Classical_gaussian_esscher_native_C1_derivative_resolvent_with_variance
-- name    : AvramDividend.Classical.gaussian_esscher_native_C1_derivative_resolvent_with_variance
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-25T12:51:06.085417+00:00
-- url     : https://prove2.me/theorems/c875ee9f-8374-4650-9cb9-3e6a10d6b3bc
-- title:
--   Gaussian native C1 Esscher derivative resolvent with explicit variance coefficient
-- statement:
--   For any positive Gaussian coefficient and positive Esscher root, the q-scale's positive Esscher tilt solves the canonical integrated Volterra equation with leading coefficient sigma squared divided by two, and the very same native kernel admits a derivative resolvent g continuous on nonnegative times and C1 on positive times, with that same explicit coefficient. This strengthens the previously Proved existential-coefficient C1 resolvent by retaining its certified native Gaussian witness and is an exact analytic input for the one-sided scale-function origin normalisation.
-- source:
--   Direct extraction from previously accepted Gaussian C1 resolvent proof, composing native double-tail full regularity, canonical Volterra identity, and antitone-kernel C1 resolvent.

import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
import Mathlib.Tactic.Positivity
import Mathlib.Analysis.Complex.Exponential
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Theorems.Thm_AvramDividend_Classical_gaussian_native_double_tail_kernel_full_regularity
import Theorems.Thm_AvramDividend_Classical_gaussian_esscher_canonical_volterra_identity_of_positive_sigma
import Theorems.Thm_AvramDividend_Classical_causal_gaussian_C1_volterra_resolvent_from_antitone_kernel
open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

namespace AvramDividend.Classical
/-- The native Gaussian Esscher scale has a C1 derivative resolvent with the exact variance coefficient. -/
theorem gaussian_esscher_native_C1_derivative_resolvent_with_variance
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (q : ℝ) (hq : 0 < q)
    (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (hσ : 0 < X.σ)
    (φ : ℝ) (hφ : 0 < φ) (hroot : X.ψ φ = q)
    (V : ℝ → ℝ)
    (hV : ∀ x : ℝ, 0 < x → V x = Real.exp (-(φ * x)) * W x) :
    ∃ (β : ℝ) (K g : ℝ → ℝ),
      IntegrableOn K (Ioi (0 : ℝ)) volume ∧
      ContinuousOn g (Ici (0 : ℝ)) ∧
      ContDiffOn ℝ 1 g (Ioi (0 : ℝ)) ∧
      (∀ x : ℝ, 0 < x →
        (X.σ ^ 2 / 2) * V x +
          (∫ s in Ioc (0 : ℝ) x,
            (β + K (x - s)) * V s ∂volume) = x) ∧
      (∀ x : ℝ, 0 < x →
        (X.σ ^ 2 / 2) * g x +
          (∫ s in Ioc (0 : ℝ) x,
            (β + K (x - s)) * g s ∂volume) = 1) := by
  sorry
end AvramDividend.Classical
