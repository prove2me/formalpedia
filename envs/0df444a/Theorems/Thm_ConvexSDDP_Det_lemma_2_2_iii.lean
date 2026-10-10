-- Prove2me | Theorems.Thm_ConvexSDDP_Det_lemma_2_2_iii
-- name    : ConvexSDDP.Det.lemma_2_2_iii
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T20:09:39.046047+00:00
-- url     : https://prove2.me/theorems/5178a65a-3839-4811-b2bd-c4a593197d1d
-- title:
--   Lemma 2.2 (iii), p. 8 — the multipliers $(\beta^k_t)_{k}$ are bounded
-- statement:
--   Under assumptions (H₁), for every run of the cutting-plane method and every stage $t=0,\dots,T-1$, the sequence of Lagrange multipliers $(\beta^k_t)_{k\ge1}$ is bounded in $\mathbb R^d$.
--
--   Bounded multipliers make the cuts uniformly Lipschitz (Corollary 2.1); the extended relatively complete recourse assumption (H₁)(6) is what provides the bound.
--
--   **Formalization Note** States live in $\mathbb R^d$ (`EuclideanSpace ℝ (Fin d)`) and controls in $\mathbb R^p$; values are in $\overline{\mathbb R}$ (`EReal`). The model satisfies `Model.H1`, i.e. (H₁)(1)–(6) of p. 4 together with three standing assumptions the section's proofs use but (H₁) does not list: $T>0$ ("Let $T$ be a positive integer"), every $\mathcal X_t$ ($t\le T$) is convex and compact (used on pp. 5, 8, 11), and $x_0\in\mathcal X_0$ ((1c)–(1d)). The run is the predicate `Model.IsRun`: any minimizer $u^k_t$, any multiplier $\beta^k_t$; the paper's iteration $k\ge 1$ is Lean's `k + 1`, and the approximation `approx k` is $V^k$. While $V^{k-1}_{t+1}\equiv-\infty$ (finitely many iterations at the start) $\theta^k_t=-\infty$ and the multiplier inequality is void, so those finitely many $\beta^k_t$ are arbitrary vectors of the direction space; the statement, as printed, holds for the whole sequence. The explicit bound (16) is not stated: its $\min V^1_t$ is $-\infty$ for $t<T-1$.
-- source:
--   Girardeau, Leclère & Philpott, On the Convergence of Decomposition Methods for Multistage Stochastic Convex Programs, author's version hal-01208295v1, p. 8, Lemma 2.2 (iii)

import Mathlib
import Definitions.Def_ConvexSDDP_Det_Basic
import Definitions.Def_ConvexSDDP_Det_Model
open Filter Topology

namespace ConvexSDDP.Det

theorem lemma_2_2_iii {d p : ℕ} (M : Model d p) (hH1 : M.H1)
    (x : ℕ → ℕ → EuclideanSpace ℝ (Fin d)) (u : ℕ → ℕ → EuclideanSpace ℝ (Fin p))
    (θ : ℕ → ℕ → EReal) (β : ℕ → ℕ → EuclideanSpace ℝ (Fin d))
    (hrun : M.IsRun x u θ β) :
    ∀ t < M.T, Bornology.IsBounded (Set.range fun k => β (k + 1) t) := by sorry

end ConvexSDDP.Det
