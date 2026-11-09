-- Prove2me | Theorems.Thm_CBCLowerBound_EveryNorm_theorem_1
-- name    : CBCLowerBound.EveryNorm.theorem_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T11:21:52.901598+00:00
-- url     : https://prove2.me/theorems/7a30133d-cbf7-4b54-8a6e-199453c08d85
-- title:
--   Theorem 1 — in every $d$-dimensional normed space, every online algorithm for convex body chasing has competitive ratio $\ge c\,d$
-- statement:
--   There is a universal constant $c>0$ such that, for every $d\ge2$ and every norm $\|\cdot\|$ on $\mathbb R^d$, any algorithm for convex body chasing in $(\mathbb R^d,\|\cdot\|)$ has competitive ratio at least $c\,d$.
--
--   Precisely: let $X$ be a real normed space of dimension $d\ge2$, let $x_0\in X$, and let $\mathrm{Alg}$ be a deterministic or randomized online algorithm for chasing nonempty closed convex sets $K_1,\dots,K_T\subseteq X$ starting at $x_0$, where $T$ is unknown in advance. If for some $R\in\mathbb R$
--   $$\mathbb E\big[\mathrm{Alg}(K_1,\dots,K_T)\big]\le R\cdot\mathrm{Opt}(K_1,\dots,K_T)$$
--   for every finite sequence of nonempty closed convex sets, then $R\ge c\,d$. The constant $c$ does not depend on $d$, on the norm, on $x_0$ or on the algorithm.
--
--   The bound matches the $O(d)$ competitive ratio of Sellke's functional Steiner point algorithm in every norm, so it is optimal up to the constant; in particular no norm, the Euclidean one included, admits a sublinear competitive ratio.
--
--   **Formalization Note** The chasing model (bodies, algorithms, expected cost, $\mathrm{Opt}$, competitiveness) is the definition `Chasing` of this mission. A randomized algorithm is a probability space of seeds with a deterministic online algorithm per seed and measurable decisions. "$\mathrm{CR}\ge cd$" is stated as "every $R$ for which the algorithm is $R$-competitive satisfies $cd\le R$", which also covers an infinite competitive ratio and avoids a ratio with $\mathrm{Opt}=0$.
--
--   Differences from the source:
--   - encoding: every norm on ℝ^d → every real normed space X with FiniteDimensional ℝ X and finrank ℝ X = d; reason: every norm on ℝ^d gives such an X and every such X is linearly isometric to ℝ^d with a norm
--   - encoding: competitive ratio CR(Alg) = sup Alg/Opt ≥ c·d → every R with E[Alg(σ)] ≤ R·Opt(σ) for all finite sequences of bodies satisfies c·d ≤ R; reason: CR(Alg) is the infimum of such R
--   - encoding: randomized algorithm and its expected cost → a probability space of seeds, a deterministic online algorithm per seed with measurable decisions, and the lower Lebesgue integral of the movement; reason: measurability of the decisions is what makes "expected cost" meaningful; deterministic algorithms are the one-point case
--   - encoding: the starting point x₀ → universally quantified x₀ ∈ X; reason: the paper fixes an arbitrary starting point
-- source:
--   Nicolas Christianson, A Linear Lower Bound for Convex Body Chasing in Every Norm, STOC 2027 submission #674 (October 2026), p.2, Theorem 1 (proof pp.16–17), https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/674.pdf

import Mathlib
import Definitions.Def_CBCLowerBound_EveryNorm_Chasing

namespace CBCLowerBound.EveryNorm

/-- **Theorem 1** (Christianson, STOC 2027 #674, p.2). There is a universal constant `c > 0`
such that, for every `d ≥ 2` and every norm on `ℝ^d` (every `d`-dimensional real normed space
`X`), every start point `x₀` and every (deterministic or randomized) online algorithm for convex
body chasing in `X`, the competitive ratio is at least `c·d`: every `R` for which the algorithm
is `R`-competitive satisfies `c·d ≤ R`. -/
theorem theorem_1 : ∃ c : ℝ, 0 < c ∧ ∀ d : ℕ, 2 ≤ d →
    ∀ (X : Type) [NormedAddCommGroup X] [NormedSpace ℝ X] [FiniteDimensional ℝ X],
      Module.finrank ℝ X = d →
      ∀ (x₀ : X) (A : RandomizedAlgorithm X x₀) (R : ℝ), A.IsCompetitive R → c * d ≤ R := by sorry

end CBCLowerBound.EveryNorm
