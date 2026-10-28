-- Prove2me | Theorems.Thm_AvramDividend_Classical_chat04_killed_semigroup_constant_of_laplace_and_rightCont
-- name    : AvramDividend.Classical.chat04_killed_semigroup_constant_of_laplace_and_rightCont
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-26T10:13:51.237379+00:00
-- url     : https://prove2.me/theorems/fe54e33e-a183-463c-94fc-c82b52ff64cd
-- title:
--   Killing-semigroup constant value from right continuity and Laplace identity
-- statement:
--   A nonnegative right-continuous killed-semigroup expected reward whose Laplace transform agrees with a nonnegative constant for all sufficiently large parameters equals that constant at every nonnegative time, provided its value at time zero is already the constant. This packages an existing Prove2Me Laplace-uniqueness theorem for the unbounded-variation killed q-scale harmonicity target.
-- source:
--   Direct specialisation of the Proved continuous_rightContinuous_Ioi_eq_of_laplace_eq with a constant comparator and a separate zero-time identity.

import Theorems.Thm_AvramDividend_Classical_continuous_rightContinuous_Ioi_eq_of_laplace_eq
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

open MeasureTheory Set AvramDividend.Classical

theorem AvramDividend.Classical.chat04_killed_semigroup_constant_of_laplace_and_rightCont
    (g : ℝ → ℝ) (c b : ℝ) (hc : 0 ≤ c)
    (hgzero : g 0 = c)
    (hgright : ∀ x : ℝ, 0 < x → ContinuousWithinAt g (Ici x) x)
    (hgmeas : AEMeasurable g (volume.restrict (Ioi 0)))
    (hgnonneg : ∀ x : ℝ, 0 < x → 0 ≤ g x)
    (hlap : ∀ θ : ℝ, b < θ →
      IntegrableOn (fun x : ℝ => Real.exp (-θ * x) * c) (Ioi 0) ∧
      IntegrableOn (fun x : ℝ => Real.exp (-θ * x) * g x) (Ioi 0) ∧
      (∫ x in Ioi (0 : ℝ), Real.exp (-θ * x) * c) =
        ∫ x in Ioi (0 : ℝ), Real.exp (-θ * x) * g x) :
    ∀ t : ℝ, 0 ≤ t → g t = c := by sorry
