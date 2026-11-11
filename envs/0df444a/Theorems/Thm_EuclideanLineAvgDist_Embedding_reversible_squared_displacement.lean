-- Prove2me | Theorems.Thm_EuclideanLineAvgDist_Embedding_reversible_squared_displacement
-- name    : EuclideanLineAvgDist.Embedding.reversible_squared_displacement
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-10T07:12:51.456058+00:00
-- url     : https://prove2.me/theorems/ce85c860-52a2-4b76-8e0a-4b4d6d858757
-- title:
--   Lemma 2.3 — squared displacement of a stationary reversible chain grows at most linearly
-- statement:
--   Let $\Omega$ be a measurable space, $\varphi:\Omega\to\mathbb R^k$ a measurable map, $P$ a Markov transition kernel on $\Omega$ and $\pi$ a probability measure on $\Omega$ such that $P$ is reversible with respect to $\pi$ (detailed balance; in particular $\pi$ is stationary). Let $x_0,x_1,\dots$ be the Markov chain with transition kernel $P$ and $x_0\sim\pi$. Then for every integer $i\ge1$,
--   $$\mathbb E\,\|\varphi(x_i)-\varphi(x_0)\|_2^2\;\le\; i\;\mathbb E\,\|\varphi(x_1)-\varphi(x_0)\|_2^2 ,$$
--   where $(x_0,x_i)$ has law $\pi(dx)P^i(x,dy)$ and both expectations are taken in $[0,\infty]$.
--
--   Taking $\Omega=X\subset\mathbb R^k$ and $\varphi$ the inclusion gives the source's statement for a reversible chain on $X$ started from its stationary distribution. In the paper this bounds how far the random walk built from Gaussian matchings travels (Section 6).
--
--   **Formalization Note** Expectations are extended nonnegative integrals; infinite second moments are allowed, and then the right-hand side is $+\infty$. No finiteness of the state space, irreducibility or laziness is assumed. The $i$-step kernel is the $i$-fold composition of $P$.
--
--   Differences from the source:
--   - generalization: a chain on a set $X\subset\mathbb R^k$ → a chain on an arbitrary measurable space $\Omega$ placed in $\mathbb R^k$ by a measurable map $\varphi$; reason: taking $\Omega=X$ with the subspace σ-algebra and $\varphi$ the inclusion recovers the source's statement
--   - reading: "a reversible Markov chain, with $x_0$ sampled from a stationary distribution" → $P$ satisfies detailed balance with respect to the law $\pi$ of $x_0$; reason: the standard meaning of a stationary reversible chain (Ostrovskii's Markov type); stationarity of $\pi$ follows from detailed balance
--   - encoding: $\mathbb E\|x_i-x_0\|_2^2$ → extended nonnegative integral against $\pi(dx)P^i(x,dy)$; reason: the joint law of $(x_0,x_i)$; values in $[0,\infty]$ cover every instance, the inequality being trivial when the right side is infinite
-- source:
--   Jack Spalding-Jamieson, STOC 2027 submission #1643 (October 2026), p. 6, Lemma 2.3

import Mathlib
import Definitions.Def_EuclideanLineAvgDist_Embedding_Basic
import Definitions.Def_EuclideanLineAvgDist_Embedding_Markov

open scoped BigOperators ENNReal
open MeasureTheory ProbabilityTheory
set_option autoImplicit false

namespace EuclideanLineAvgDist.Embedding

/-- Lemma 2.3 (p. 6). Let `x₀, x₁, …` be a Markov chain with transition kernel `P` on a measurable
state space `Ω`, placed in `ℝᵏ` by a measurable map `φ`, with `x₀ ∼ π` for a probability measure
`π` with respect to which `P` is reversible (detailed balance; hence `π` is stationary). Then for
every integer `i ≥ 1`, `E ‖φ(xᵢ) - φ(x₀)‖₂² ≤ i · E ‖φ(x₁) - φ(x₀)‖₂²`, where the law of
`(x₀, xᵢ)` is `π(dx) Pⁱ(x,dy)` and expectations are extended nonnegative integrals (possibly `∞`). -/
theorem reversible_squared_displacement {Ω : Type*} [MeasurableSpace Ω] {k : ℕ}
    (φ : Ω → Eucl k) (hφ : Measurable φ)
    (P : Kernel Ω Ω) [IsMarkovKernel P] (π : Measure Ω) [IsProbabilityMeasure π]
    (hrev : IsReversible π P) (i : ℕ) (hi : 1 ≤ i) :
    sqDisplacement φ (π ⊗ₘ kernelIter P i) ≤ (i : ℝ≥0∞) * sqDisplacement φ (π ⊗ₘ P) := by sorry

end EuclideanLineAvgDist.Embedding
