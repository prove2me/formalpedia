-- Prove2me | Theorems.Thm_BerryEsseenFeller_berry_esseen
-- name    : BerryEsseenFeller.berry_esseen
-- status  : Open
-- author  : @Nickrobbins95
-- created : 2026-10-05T01:37:57.845982+00:00
-- url     : https://prove2.me/theorems/456131bd-0fa5-4289-95d3-09a5f825da8e
-- title:
--   Berry–Esseen theorem: $|F_n(x)-\Phi(x)| \le \dfrac{3\rho}{\sigma^3\sqrt n}$
-- statement:
--   This is the Berry–Esseen theorem, the classical quantitative form of the central limit theorem, in the version with the explicit constant $3$ proved in Feller's and Durrett's textbooks.
--
--   Let $X_1, X_2, \dots$ be independent and identically distributed real random variables on a probability space $(\Omega, \mathcal F, \mathbb P)$ such that
--
--   $$
--   \mathbb E X_1 = 0, \qquad \mathbb E X_1^2 = \sigma^2 > 0, \qquad \rho = \mathbb E|X_1|^3 < \infty .
--   $$
--
--   For $n \ge 1$ let $F_n$ be the distribution function of the normalized sum,
--
--   $$
--   F_n(x) = \mathbb P\!\left( \frac{X_1 + \cdots + X_n}{\sigma \sqrt n} \le x \right), \qquad x \in \mathbb R,
--   $$
--
--   and let $\Phi(x) = \frac{1}{\sqrt{2\pi}} \int_{-\infty}^{x} e^{-t^2/2}\, dt$ be the standard normal distribution function. Then for every $n \ge 1$ and every real $x$,
--
--   $$
--   \bigl| F_n(x) - \Phi(x) \bigr| \le \frac{3\rho}{\sigma^3 \sqrt n}.
--   $$
--
--   The central limit theorem only asserts that $F_n(x) \to \Phi(x)$. The Berry–Esseen theorem turns this into an explicit error bound of order $n^{-1/2}$ that is uniform in $x$ and depends on the common distribution only through the ratio $\rho/\sigma^3$; the order $n^{-1/2}$ cannot be improved in general (for instance for symmetric $\pm 1$ steps). It is the standard tool for quantifying normal approximations of sums of independent variables. Smaller admissible values of the absolute constant are known; the constant $3$ is the one in the cited textbook statements.
--
--   **Formalization Note** The sequence is `X : ℕ → Ω → ℝ` indexed from $0$, so $X_k$ of the text is `X (k - 1)` and $X_1 + \cdots + X_n$ is `∑ i ∈ Finset.range n, X i ω`. The i.i.d. assumption is `iIndepFun X P` together with `IdentDistrib (X i) (X 0) P P` for every `i`, exactly as in Mathlib's central limit theorem `ProbabilityTheory.tendstoInDistribution_inv_sqrt_mul_sum_sub`. Finiteness of the third absolute moment is the hypothesis that $|X_1|^3$ is integrable; on a probability space this also makes $X_1$ and $X_1^2$ integrable, so the Bochner integrals in the hypotheses $\mathbb E X_1 = 0$ and $\mathbb E X_1^2 = \sigma^2$ are genuine expectations, and $\rho$ is named by the hypothesis $\int |X_1|^3 \, d\mathbb P = \rho$. $F_n(x)$ is `ProbabilityTheory.cdf` of the law `P.map` of the normalized sum, and $\Phi$ is `cdf (gaussianReal 0 1)`. The hypotheses $\sigma > 0$ and $n \ge 1$ are part of the source statement and are needed: for $n = 0$ Lean's convention $a / 0 = 0$ would make the right-hand side $0$.
-- source:
--   W. Feller, An Introduction to Probability Theory and Its Applications, Vol. II, 2nd ed., Wiley (1971), Chapter XVI (Expansions related to the central limit theorem), Section 5 (Berry–Esseen theorems), Theorem 1: for i.i.d. X_k with E(X_k) = 0, E(X_k^2) = sigma^2 > 0, E(|X_k|^3) = rho < infinity and F_n the distribution of (X_1 + ... + X_n)/(sigma sqrt n), |F_n(x) - N(x)| <= 3 rho/(sigma^3 sqrt n) for all x and n. Also R. Durrett, Probability: Theory and Examples, 5th ed., Cambridge University Press (2019), Section 3.4.4 (Rates of convergence (Berry–Esseen)), Theorem 3.4.17 (Theorem 3.4.9 in the 4th ed.), same statement with constant 3. Original papers: A. C. Berry, The accuracy of the Gaussian approximation to the sum of independent variates, Trans. Amer. Math. Soc. 49 (1941), 122–136; C.-G. Esseen, On the Liapounoff limit of error in the theory of probability, Ark. Mat. Astr. Fys. 28A (1942), no. 9, 1–19.

import Mathlib

open MeasureTheory ProbabilityTheory

namespace BerryEsseenFeller

/-- **Berry–Esseen theorem** with Feller's constant `3` (Feller, Vol. II, Ch. XVI, §5, Theorem 1;
Durrett, *Probability: Theory and Examples*, 5th ed., Theorem 3.4.17).

`X 0, X 1, …` are i.i.d. real random variables (`iIndepFun` plus `IdentDistrib (X i) (X 0)`) with
`E X = 0`, `E X² = σ²`, `σ > 0`, and `E|X|³ = ρ < ∞`. For every `n ≥ 1` and every real `x`, the
distribution function of `(X 0 + ⋯ + X (n - 1)) / (σ √n)` (the `cdf` of its law `P.map _`) differs
from the standard normal distribution function `cdf (gaussianReal 0 1)` at `x` by at most
`3 ρ / (σ³ √n)`. -/
theorem berry_esseen {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {X : ℕ → Ω → ℝ} (hindep : iIndepFun X P) (hident : ∀ i, IdentDistrib (X i) (X 0) P P)
    {σ ρ : ℝ} (hσ : 0 < σ) (h3 : Integrable (fun ω => |X 0 ω| ^ 3) P)
    (hmean : ∫ ω, X 0 ω ∂P = 0) (hvar : ∫ ω, X 0 ω ^ 2 ∂P = σ ^ 2)
    (hρ : ∫ ω, |X 0 ω| ^ 3 ∂P = ρ) (n : ℕ) (hn : 0 < n) (x : ℝ) :
    |cdf (P.map (fun ω => (∑ i ∈ Finset.range n, X i ω) / (σ * √(n : ℝ)))) x
        - cdf (gaussianReal 0 1) x| ≤ 3 * ρ / (σ ^ 3 * √(n : ℝ)) := by sorry

end BerryEsseenFeller
