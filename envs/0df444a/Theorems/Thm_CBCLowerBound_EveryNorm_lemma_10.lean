-- Prove2me | Theorems.Thm_CBCLowerBound_EveryNorm_lemma_10
-- name    : CBCLowerBound.EveryNorm.lemma_10
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-11-08T11:21:04.045922+00:00
-- url     : https://prove2.me/theorems/850351d3-46aa-4822-8b9f-9f4d9d338814
-- title:
--   Lemma 10 (Milman) — every $d$-dimensional normed space has a subspace with a quotient onto $\mathbb R^k$, $k\ge d/2$, with $B_2^k\subseteq Q(B_E)\subseteq M B_2^k$
-- statement:
--   There is a universal constant $M\ge1$ such that, for every $d$-dimensional real normed vector space $X$, there are a subspace $E\subseteq X$, an integer $k\ge d/2$ and a linear map $Q:E\to\mathbb R^k$ satisfying
--   $$B_2^k\subseteq Q(B_E)\subseteq M\cdot B_2^k,$$
--   where $B_E=\{x\in E:\|x\|_X\le1\}$ is the unit ball of $E$ and $B_2^k$ is the (closed) Euclidean unit ball of $\mathbb R^k$.
--
--   This is Milman's quotient-of-a-subspace theorem (Proc. AMS 1985) in the form used by the paper: the first inclusion lifts Euclidean movements to $E$ at no greater cost, the second bounds the cost of projecting a trajectory from $E$ to $\mathbb R^k$, which transfers the Euclidean case of Proposition 9 to an arbitrary norm.
--
--   Differences from the source:
--   - encoding: ℝ^k with the Euclidean norm → EuclideanSpace ℝ (Fin k); reason: Mathlib's Euclidean space
--   - encoding: "d-dimensional normed vector space" and "k ≥ d/2" → a finite-dimensional real normed space with d = finrank, and (finrank : ℝ)/2 ≤ k; reason: same spaces; the inequality is read over the reals
-- source:
--   Nicolas Christianson, A Linear Lower Bound for Convex Body Chasing in Every Norm, STOC 2027 submission #674 (October 2026), p.15, Lemma 10 (citing V. D. Milman, Proc. AMS 94(3):445–449, 1985), https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/674.pdf

import Mathlib

namespace CBCLowerBound.EveryNorm

/-- **Lemma 10** (Milman's quotient-of-a-subspace theorem, [Mil85]; Christianson, STOC 2027
#674, p.15). There is a universal constant `M ≥ 1` such that, for every finite-dimensional real
normed space `X` of dimension `d`, there are a subspace `E ⊆ X`, an integer `k ≥ d/2` and a
linear map `Q : E → ℝ^k` with `B₂ᵏ ⊆ Q(B_E) ⊆ M · B₂ᵏ`, where `B_E = {x ∈ E : ‖x‖_X ≤ 1}` and
`B₂ᵏ` is the closed Euclidean unit ball of `ℝ^k`. -/
theorem lemma_10 : ∃ M : ℝ, 1 ≤ M ∧
    ∀ (X : Type) [NormedAddCommGroup X] [NormedSpace ℝ X] [FiniteDimensional ℝ X],
      ∃ (E : Submodule ℝ X) (k : ℕ) (Q : E →ₗ[ℝ] EuclideanSpace ℝ (Fin k)),
        (Module.finrank ℝ X : ℝ) / 2 ≤ k ∧
        Metric.closedBall (0 : EuclideanSpace ℝ (Fin k)) 1 ⊆ Q '' {x : E | ‖x‖ ≤ 1} ∧
        Q '' {x : E | ‖x‖ ≤ 1} ⊆ Metric.closedBall (0 : EuclideanSpace ℝ (Fin k)) M := by sorry

end CBCLowerBound.EveryNorm
