-- Prove2me | Theorems.Thm_AvramDividend_Classical_psi_eventually_positive_quadratic_of_gaussian
-- name    : AvramDividend.Classical.psi_eventually_positive_quadratic_of_gaussian
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-06T17:42:31.46229+00:00
-- url     : https://prove2.me/theorems/ea687ee2-8799-43bb-8064-646616de74f8
-- title:
--   Eventual positivity and quadratic upper bound for the Gaussian Lévy exponent
-- statement:
--   If the canonical spectrally negative Lévy process has nonzero Gaussian coefficient, then above one nonnegative cutoff β the exponent is greater than any fixed q and its excess ψ(θ)−q is bounded by C(1+θ²) for a finite nonnegative constant C. The estimate follows from already established Lévy exponent quadratic growth and Gaussian eventual positivity, and supplies the exact input needed for strict scale-function positivity.
-- source:
--   Compose the Gaussian eventual positivity lemma and psi_quadratic_upper using C0 = abs(c)+sigma^2/2+small-jump second moment. Choose beta=max(1,beta0) and C=abs(C0)+abs(q) to avoid any unproved sign assumption on C0. Two theorem imports permit bounded import parsing.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open MeasureTheory Set
open scoped NNReal ENNReal

namespace AvramDividend.Classical

theorem psi_eventually_positive_quadratic_of_gaussian
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (q : ℝ) (hσ : 0 < X.σ) :
    ∃ β C : ℝ, 0 ≤ β ∧ 0 ≤ C ∧
      ∀ θ : ℝ, β ≤ θ →
        q < X.ψ θ ∧ X.ψ θ - q ≤ C * (1 + θ ^ 2) := by
  sorry

end AvramDividend.Classical
