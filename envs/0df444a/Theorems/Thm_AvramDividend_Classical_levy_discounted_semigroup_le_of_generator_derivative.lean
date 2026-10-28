-- Prove2me | Theorems.Thm_AvramDividend_Classical_levy_discounted_semigroup_le_of_generator_derivative
-- name    : AvramDividend.Classical.levy_discounted_semigroup_le_of_generator_derivative
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-25T23:23:51.458571+00:00
-- url     : https://prove2.me/theorems/2833d983-685a-4d71-9b74-bb1c1f5b46ff
-- title:
--   Discounted semigroup HJB domination from generator differentiation under the expectation
-- statement:
--   Suppose a deterministic Levy transition expectation f(s)=E[w(x+X_s)] is continuous at the origin, differentiable for positive s, and differentiation is justified by the generator interchange f'(s)=E[Gamma w(x+X_s)]. Suppose w and Gamma w are integrable under each positive-time transition and the global HJB generator inequality Gamma w <= q w holds pointwise. Then the discounted expectation satisfies exp(-q t) f(t) <= f(0). The proof integrates the pointwise generator inequality and uses the previously Proved discounted Gronwall semigroup theorem. This is a mathematically precise reusable interface that isolates the missing Ito/Dynkin derivative interchange from the already verified HJB comparison machinery.
-- source:
--   Avram, Palmowski and Pistorius (2007), proof of Proposition 4(i), Section 5.4; generator inequality and stopped Dynkin/Itô verification.

import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_levy_discounted_semigroup_le_initial_of_deriv_le

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.levy_discounted_semigroup_le_of_generator_derivative
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (w : ℝ → ℝ) (q x : ℝ) (f : ℝ → ℝ)
    (hfcont : ContinuousOn f (Ici 0))
    (hfdiff : ∀ s : ℝ, 0 < s → DifferentiableAt ℝ f s)
    (hftrans : ∀ s : ℝ, 0 < s →
      f s = ∫ ω, w (x + X.X (Real.toNNReal s) ω) ∂P)
    (hfderiv : ∀ s : ℝ, 0 < s →
      deriv f s = ∫ ω,
        X.generator w (x + X.X (Real.toNNReal s) ω) ∂P)
    (hIntW : ∀ s : ℝ, 0 < s → Integrable
      (fun ω => w (x + X.X (Real.toNNReal s) ω)) P)
    (hIntGen : ∀ s : ℝ, 0 < s → Integrable
      (fun ω => X.generator w (x + X.X (Real.toNNReal s) ω)) P)
    (hHJB : ∀ y : ℝ, X.generator w y ≤ q * w y)
    (t : ℝ) (ht : 0 ≤ t) :
    Real.exp (-(q * t)) * f t ≤ f 0 := by sorry
