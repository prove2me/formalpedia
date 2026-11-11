-- Prove2me | Theorems.Thm_EuclideanLineAvgDist_Embedding_gaussian_transition_bound
-- name    : EuclideanLineAvgDist.Embedding.gaussian_transition_bound
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-10T07:12:48.23894+00:00
-- url     : https://prove2.me/theorems/ad7bd638-6103-4605-8e73-9cbcfd392dc6
-- title:
--   Lemma 2.1 — Gaussian projections of a symmetric random step
-- statement:
--   There is a universal constant $C>0$ with the following property. Let $k\ge0$, let $X\subset\mathbb R^k$ be a set of size $n$, and for each $g\in\mathbb R^k$ let $K_g$ be a symmetric matrix on $X$ with nonnegative entries and row sums equal to $1$, depending measurably on $g$. Sample $x_0\sim\mathrm{Unif}(X)$ and $\gamma\sim N(0,I_k)$ independently, then sample $x_1$ from $K_\gamma(x_0,\cdot)$. Then
--   $$\bigl(\mathbb E\,|\langle\gamma,x_1-x_0\rangle|\bigr)^2\;\le\;C\;\mathbb E\,\|x_1-x_0\|_2^2\cdot\frac{\log n}{\log\log n}\qquad(n\ge3),$$
--   and, for every $n$, the same inequality with $\log n/\log\log n$ replaced by $\rho(n)=\log\max(3,n)/\log\log\max(3,n)$.
--
--   This is the source's bound $(\mathbb E|\langle\gamma,x_1-x_0\rangle|)^2=O\bigl(\mathbb E\|x_1-x_0\|_2^2\,\frac{\log n}{\log\log n}\bigr)$ with its constant made explicit as an existential quantifier placed before $k$, $X$ and $K$. The paper's proof (p. 15) gives $C=4(3+2\log2)$ for $n\ge3$.
--
--   **Formalization Note** The two expectations are integrals against the Gaussian measure of the explicit averages $\frac1n\sum_{x,y}K_g(x,y)(\cdot)$, which is the joint law of $(\gamma,x_0,x_1)$. The matrices may depend arbitrarily (but measurably) on $g$; $x_1$ need not be independent of $\gamma$.
--
--   Differences from the source:
--   - encoding: $O(\cdot)$ → $\exists C>0$ placed before all of $k$, $X$, $(K_g)$; reason: the meaning of the source's $O$ with a universal constant
--   - generalization: rate $\log n/\log\log n$, undefined or nonpositive for $n\le2$ → $\rho(n)$ with $n$ replaced by $\max(3,n)$, so the bound is claimed for every $n$; reason: equal for $n\ge3$, which is the source's claim; for $n=1$ both sides vanish and for $n=2$ the bound holds by Cauchy–Schwarz
--   - encoding: $K_g$ for each $g$ → in addition $g\mapsto K_g(x,y)$ is measurable; reason: implicit in "sample $x_1$ from $K_\gamma(x_0,\cdot)$"; it excludes only families for which the source's expectation is undefined
--   - encoding: expectations under the sampling procedure → Gaussian integrals of $\frac1n\sum_{x,y}K_g(x,y)(\cdot)$; reason: this is the joint law of $(\gamma,x_0,x_1)$; same values
-- source:
--   Jack Spalding-Jamieson, STOC 2027 submission #1643 (October 2026), p. 5, Lemma 2.1

import Mathlib
import Definitions.Def_EuclideanLineAvgDist_Embedding_Basic
import Definitions.Def_EuclideanLineAvgDist_Embedding_Markov

open scoped BigOperators
open MeasureTheory ProbabilityTheory
set_option autoImplicit false

namespace EuclideanLineAvgDist.Embedding

/-- Lemma 2.1 (p. 5). There is a universal constant `C > 0` such that for every `k`, every finite
`X ⊂ ℝᵏ` of size `n`, and every measurable family `(K_g)_{g ∈ ℝᵏ}` of symmetric nonnegative
row-stochastic matrices on `X`, sampling `x₀ ∼ Unif(X)`, `γ ∼ N(0, I_k)` independently and then
`x₁ ∼ K_γ(x₀, ·)`,
`(E |⟨γ, x₁ - x₀⟩|)² ≤ C · E ‖x₁ - x₀‖₂² · (log n / log log n)`
(with `n` replaced by `max 3 n` inside the rate). -/
theorem gaussian_transition_bound :
    ∃ C : ℝ, 0 < C ∧ ∀ (k : ℕ) (X : Finset (Eucl k)) (K : Eucl k → X → X → ℝ),
      IsGaussianTransitionFamily X K →
        projectionMean X K ^ 2 ≤ C * squaredStepMean X K * logRate X.card := by sorry

end EuclideanLineAvgDist.Embedding
