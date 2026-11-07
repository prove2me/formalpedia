-- Prove2me | Theorems.Thm_CompNonlocal_lemma_16_randomized_normalization
-- name    : CompNonlocal.lemma_16_randomized_normalization
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T22:39:06.64471+00:00
-- url     : https://prove2.me/theorems/7c03c27d-c865-470f-8162-0a41ff375859
-- title:
--   Lemma 16, p.43 — randomized normalization: $\mathbb E_n\|n-r\|^2\le2\|q-r\|^2$, constant 2 optimal
-- statement:
--   For $q\in\mathbb R^3$ let $\rho=\|q\|_2$ and $\pi=\min\{1,\rho(\rho+2)\}$. Let $n$ equal $q/\rho$ with probability $(1+\pi)/2$ and $-q/\rho$ otherwise; if $q=0$, let $n=\pm e_3$ with probability $1/2$ each. Then for every unit vector $r\in S^2$,
--   $$\mathbb E_n\|n-r\|_2^2\le2\,\|q-r\|_2^2 .$$
--   The constant $2$ is optimal: for every, possibly randomized, rule mapping $q$ to a unit vector and every $c<2$, there are $q$ and a unit $r$ with $\mathbb E\|n-r\|_2^2>c\,\|q-r\|_2^2$.
--
--   It turns any receiver estimate of the Bloch vector into a unit direction at a factor-2 cost, as needed to apply Lemma 15.
--
--   Differences from the source:
--   - encoding: E_n over the random unit vector n; 'any, possibly randomized, rule' → the explicit two-point average; a rule is a map K from ℝ³ to probability measures on S²; reason: the same expectations
-- source:
--   Głuch, Morimae, From Computational Nonlocality to Public-Key Encryption and Commitments, manuscript (STOC 2027 submission, sha256 e245edd7…), Lemma 16, p.43

import Mathlib

set_option autoImplicit false

open MeasureTheory

namespace CompNonlocal

/-- **Lemma 16 (Randomized normalization).** Głuch, Morimae, *From Computational Nonlocality to
Public-Key Encryption and Commitments*, manuscript (STOC 2027 submission, sha256 e245edd7…), p.43:
"For q ∈ R³ let ρ = ∥q∥₂ and π = min{1, ρ(ρ + 2)}. Let n be the random unit vector equal to q/ρ with
probability (1 + π)/2 and to −q/ρ otherwise; if q = 0, let n = ±e₃ with probability 1/2 each. Then,
for every unit vector r ∈ S², E_n∥n − r∥₂² ≤ 2∥q − r∥₂². The constant 2 is optimal for any, possibly
randomized, rule mapping q to a unit vector."

**Formalization Note** `E_n` is written as the explicit two-point average; `e₃` is
`EuclideanSpace.single 2 1`. Optimality: for every rule `K` sending each `q` to a probability
measure on the unit sphere and every `c < 2`, some `q` and unit `r` have
`∫ ‖n − r‖² dK(q) > c ‖q − r‖²`. -/
theorem lemma_16_randomized_normalization :
    (∀ q r : EuclideanSpace ℝ (Fin 3), ‖r‖ = 1 →
      (if q = 0 then
          (1 / 2) * ‖EuclideanSpace.single 2 (1 : ℝ) - r‖ ^ 2 +
            (1 / 2) * ‖-EuclideanSpace.single 2 (1 : ℝ) - r‖ ^ 2
        else
          ((1 + min 1 (‖q‖ * (‖q‖ + 2))) / 2) * ‖‖q‖⁻¹ • q - r‖ ^ 2 +
            ((1 - min 1 (‖q‖ * (‖q‖ + 2))) / 2) * ‖-(‖q‖⁻¹ • q) - r‖ ^ 2) ≤
        2 * ‖q - r‖ ^ 2) ∧
    ∀ K : EuclideanSpace ℝ (Fin 3) → Measure (Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1),
      (∀ q, IsProbabilityMeasure (K q)) → ∀ c : ℝ, c < 2 →
        ∃ q r : EuclideanSpace ℝ (Fin 3), ‖r‖ = 1 ∧
          c * ‖q - r‖ ^ 2 < ∫ n, ‖(n : EuclideanSpace ℝ (Fin 3)) - r‖ ^ 2 ∂(K q) := by sorry

end CompNonlocal
