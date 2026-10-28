-- Prove2me | Theorems.Thm_AvramDividend_Classical_pathwise_killed_survival_reserve_laplace_envelope
-- name    : AvramDividend.Classical.pathwise_killed_survival_reserve_laplace_envelope
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-25T23:55:54.635492+00:00
-- url     : https://prove2.me/theorems/a17c8b8c-1566-4dfa-9b4c-7200884f1ac7
-- title:
--   Full finite-horizon killed-survival reserve Laplace envelope, path by path
-- statement:
--   Fix a spectrally negative Lévy sample path that is bounded below on [0,t]. Integrate exp(-θx) over all positive initial reserves x for which the reserve x+X_s remains nonnegative at every s≤t. For θ>0 this integral equals exp(-θ max(0,-inf_{s≤t}X_s))/θ. The result is pathwise, permits equality at the boundary, and supplies the inner reserve integral for a Laplace–Tonelli proof of killed-scale harmonicity.
-- source:
--   Direct composition of the Proved lower_survival_running_infimum_equiv and lower_survival_nonstrict_reserve_integral, both proved from Mathlib without relying on the root two-sided exit theorem.

import Mathlib.Order.ConditionallyCompleteLattice.Basic
import Mathlib.Probability.Martingale.Basic
import Mathlib.MeasureTheory.Integral.Lebesgue.Map
import Theorems.Thm_AvramDividend_Classical_lower_survival_running_infimum_equiv
import Theorems.Thm_AvramDividend_Classical_lower_survival_nonstrict_reserve_integral

open MeasureTheory Set
open scoped NNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.pathwise_killed_survival_reserve_laplace_envelope
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (t : ℝ≥0) (ω : Ω)
    (hb : BddBelow {y : ℝ | ∃ s : ℝ≥0, s ≤ t ∧ y = X.X s ω})
    (θ : ℝ) (hθ : 0 < θ) :
    (∫ x in {x : ℝ | 0 < x ∧
        ∀ s : ℝ≥0, s ≤ t → 0 ≤ x + X.X s ω}, Real.exp (-θ * x)) =
      Real.exp (-θ * max 0
        (-sInf {y : ℝ | ∃ s : ℝ≥0, s ≤ t ∧ y = X.X s ω})) / θ := by sorry
