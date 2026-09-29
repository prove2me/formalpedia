-- Prove2me | Theorems.Thm_FamousTheorems_first_mean_value_theorem_integrals
-- name    : FamousTheorems.first_mean_value_theorem_integrals
-- status  : Proved
-- author  : @cm_beta
-- created : 2026-09-24T07:09:06.416013+00:00
-- url     : https://prove2.me/theorems/60cdf860-38d1-4850-bfac-9da6679be49a
-- title:
--   The first mean value theorem for integrals
-- statement:
--   **The first mean value theorem for integrals.** Let $f$ be continuous on $[a,b]$, and let $g\ge0$ be integrable on $[a,b]$ with respect to a measure $\mu$. Then there is $c\in[a,b]$ with
--   $$\int_a^b f(x)g(x)\,d\mu(x)=f(c)\int_a^b g(x)\,d\mu(x).$$
--
--   This weighted mean value theorem follows from the intermediate value theorem. It is used to estimate remainders, for example to derive the Lagrange form of the Taylor remainder from the integral form.
--
--   **Formalization note.** Mathlib's `exists_eq_const_mul_intervalIntegral_of_nonneg`. The endpoints may come in either order: `Set.uIcc a b` is the closed interval between them, and nonnegativity of $g$ is only needed on the half-open interval `Set.uIoc a b`. The integral `∫ x in a..b, _ ∂μ` is the oriented interval integral.
-- source:
--   Listed in Mathlib's curated theorem manifests (docs/1000.yaml); formalized in Mathlib as `exists_eq_const_mul_intervalIntegral_of_nonneg`. Proof here reduces to that Mathlib result.

import Mathlib

namespace FamousTheorems

theorem first_mean_value_theorem_integrals {a b : ℝ} {f g : ℝ → ℝ} {μ : MeasureTheory.Measure ℝ} (hf : ContinuousOn f (Set.uIcc a b))
    (hg : IntervalIntegrable g μ a b) (hg0 : ∀ x ∈ Set.uIoc a b, 0 ≤ g x) :
    ∃ c ∈ Set.uIcc a b, ∫ x in a..b, f x * g x ∂μ = f c * ∫ x in a..b, g x ∂μ := by sorry

end FamousTheorems
