-- Prove2me | Theorems.Thm_AlmostKing_Query_theorem_12
-- name    : AlmostKing.Query.theorem_12
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T10:51:41.632448+00:00
-- url     : https://prove2.me/theorems/9070170c-0227-4ccd-b6e6-8a409183b366
-- title:
--   Theorem 12 — sparse regularity for orientations
-- statement:
--   For every real $\tau>0$ and positive integer $m$, there exist $0<\mu<1$, an integer $M\ge m$, and a threshold $N_0$ such that the following holds uniformly over $0<p\le1$ and $n\ge N_0$. If $H$ is a $(\mu,p)$-upper-uniform graph on $n$ vertices and $D$ is any orientation of $H$, there is a partition $V_0,V_1,\ldots,V_k$ with nonempty nonexceptional classes and a common class size $\ell$ with
--   $$m\le k\le M,\quad |V_i|=\ell\ (1\le i\le k),\quad |V_0|\le\tau n,$$
--   and
--   $$|\{(i,j):i\ne j,\ (V_i,V_j)\text{ is not }(\tau,p)\text{-regular in }D\}|\le\tau k^2.$$
--   The exceptional class may be empty. The regularity predicate is meaningful also for $\tau\ge1$.
--
--   This is the sparse oriented regularity statement attributed by the source to Allen, Kohayakawa, Mota and Parente.
--
--   Differences from the source:
--   - encoding: $[n]=\{1,\ldots,n\}$ → $\mathrm{Fin}\,n=\{0,\ldots,n-1\}$; reason: relabeling by an order-preserving bijection preserves all graph and counting conditions
--   - reading: an orientation of a sufficiently large graph, for any $p\in(0,1]$ → one threshold $N_0$ before $p$ and $n$; reason: the application in the proof of Lemma 7 uses $p=n^{-2/3}$, so the threshold must be uniform in $p$
--   - encoding: a partition with equal-sized nonexceptional groups → finite disjoint covering classes, nonempty nonexceptional classes, and an existential common natural size $\ell$; reason: this spells out partition and equal cardinalities without adding a condition
--   - reading: regularity is defined for $0<\alpha<1$, but Theorem 12 allows every $\tau>0$ → the same regularity formula for all positive $\tau$, including $\tau\ge1$; reason: the subset-size tests are impossible when $\tau\ge1$; disjointness and nonemptiness of the classes are retained
-- source:
--   Ziad Ismaili Alaoui, Oded Lachish, Nikhil S. Mande, A King for Almost Everyone, STOC 2027 submission #472 (October 2026), SHA-256 c262b203b2088dcae48025a77e016df4cc78f93c1856a6fac580c7577d8dea92, Theorem 12 ([AKMP14, Theorem 2.1]), p. 9. https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/472.pdf

import Mathlib
import Definitions.Def_AlmostKing_Query_Regularity

namespace AlmostKing.Query

/-- Theorem 12, p. 9, attributed there to AKMP14, Theorem 2.1.
The size threshold is uniform over p, as required by the application on p. 9. -/
theorem theorem_12 : ∀ τ : ℝ, 0 < τ → ∀ m : ℕ, 0 < m →
    ∃ μ : ℝ, 0 < μ ∧ μ < 1 ∧ ∃ M : ℕ, m ≤ M ∧ ∃ N₀ : ℕ,
    ∀ p : ℝ, 0 < p → p ≤ 1 → ∀ n : ℕ, N₀ ≤ n →
    ∀ H : SimpleGraph (Fin n), IsUpperUniform H μ p →
    ∀ D : Digraph (Fin n), IsOrientation H D →
    ∃ k ℓ : ℕ, ∃ V₀ : Finset (Fin n), ∃ groups : Fin k → Finset (Fin n),
      m ≤ k ∧ k ≤ M ∧ IsPartition V₀ groups ∧
      (∀ i, (groups i).Nonempty) ∧ (∀ i, (groups i).card = ℓ) ∧
      (irregularPairs D groups τ p : ℝ) ≤ τ * (k : ℝ)^2 ∧
      (V₀.card : ℝ) ≤ τ * n := by sorry

end AlmostKing.Query
