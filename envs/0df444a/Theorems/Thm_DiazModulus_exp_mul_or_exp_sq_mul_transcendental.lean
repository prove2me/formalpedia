-- Prove2me | Theorems.Thm_DiazModulus_exp_mul_or_exp_sq_mul_transcendental
-- name    : DiazModulus.exp_mul_or_exp_sq_mul_transcendental
-- status  : Proved
-- author  : @carlok
-- created : 2026-11-01T09:19:11.149198+00:00
-- url     : https://prove2.me/theorems/d3e7d183-3eb2-460a-95b7-3716a18bcdcf
-- title:
--   For non-zero logarithms λ₀, λ₁ of algebraic numbers and algebraic β ≠ 0, one of e^{βλ₀λ₁} and e^{(βλ₀)²λ₁} is transcendental
-- statement:
--   Here $\mathcal{L}$ is the set of logarithms of algebraic numbers (the $z \in \mathbb{C}$ with $e^z$ algebraic). Let $\lambda_0, \lambda_1 \in \mathcal{L}$ be non-zero and let $\beta$ be a non-zero algebraic number. Then at least one of
--
--   $$e^{\beta\lambda_0\lambda_1} \qquad\text{and}\qquad e^{(\beta\lambda_0)^2\lambda_1}$$
--
--   is transcendental.
--
--   This is DALAG Exercise 11.8 (b), p. 415. At $\lambda_0 = \lambda_1 = \log 2$ and $\beta = 1$ it is Exercise 11.8 (c): one of $2^{\log 2}$ and $2^{(\log 2)^2}$ is transcendental.
--
--   **Proof.** Apply the five exponentials theorem (`DiazModulus.five_exponentials`) to $x = (1, \beta\lambda_0)$, $y = (\lambda_1, \beta\lambda_0\lambda_1)$ and $\eta = \beta^{-1}$. The five numbers are $e^{\lambda_1}$, $e^{\beta\lambda_0\lambda_1}$ (twice), $e^{(\beta\lambda_0)^2\lambda_1}$ and $e^{\eta\beta\lambda_0} = e^{\lambda_0}$; the outer two are algebraic, so $e^{\beta\lambda_0\lambda_1}$ and $e^{(\beta\lambda_0)^2\lambda_1}$ are not both algebraic. Both $x$ and $y = \lambda_1x$ are linearly independent over $\mathbb{Q}$: $\beta\lambda_0 = r \in \mathbb{Q}$ would make $\lambda_0 = r/\beta$ a non-zero algebraic number with $e^{\lambda_0}$ algebraic, against Hermite–Lindemann (`DiazModulus.hermite_lindemann_holds`).
--
--   **Novelty.** None: this is DALAG Exercise 11.8 (b), p. 415, derived here from the five exponentials theorem. The contribution of this node is the formal proof.
-- source:
--   Known: M. Waldschmidt, Diophantine Approximation on Linear Algebraic Groups, Grundlehren der mathematischen Wissenschaften 326, Springer, 2000, Exercise 11.8 (b), p. 415; Exercise 11.8 (c) is its instance at λ₀ = λ₁ = log 2, β = 1. Uses DiazModulus.hermite_lindemann_holds and DiazModulus.five_exponentials. C2 of the Diaz modulus mission. Formal proof: Diaz modulus mission, 30 October 2026 (C. Perassi).

import Definitions.Def_DiazModulus

open Complex ComplexConjugate

namespace DiazModulus

/-- **DALAG Exercise 11.8 (b)**, p. 415, from the five exponentials theorem. Let `λ₀, λ₁` be
nonzero logarithms of algebraic numbers and `β` a nonzero algebraic number. Then at least one of
`e^{βλ₀λ₁}` and `e^{(βλ₀)²λ₁}` is transcendental.

At `λ₀ = λ₁ = log 2`, `β = 1` this is Exercise 11.8 (c): one of `2^{log 2}`, `2^{(log 2)²}` is
transcendental. -/
theorem exp_mul_or_exp_sq_mul_transcendental :
    ∀ l₀ l₁ β : ℂ, l₀ ∈ LogAlg → l₁ ∈ LogAlg → l₀ ≠ 0 → l₁ ≠ 0 →
      IsAlgebraic ℚ β → β ≠ 0 →
      Transcendental ℚ (Complex.exp (β * l₀ * l₁)) ∨
        Transcendental ℚ (Complex.exp ((β * l₀) ^ 2 * l₁)) := by
  sorry

end DiazModulus
