-- Prove2me | Theorems.Thm_ConstrainedQueueing_MaxThroughput_theorem_3_1
-- name    : ConstrainedQueueing.MaxThroughput.theorem_3_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T17:47:33.278439+00:00
-- url     : https://prove2.me/theorems/f1e38084-7448-4f05-b853-f6995243f1ee
-- title:
--   Theorem 3.1, pp. 1938–1939 — Foster-type drift criterion implies stability (Definition 3.1)
-- statement:
--   Let $X(t)$ be a Markov chain on a countable state space $\mathcal X$ with stochastic transition matrix $P$. Suppose there are a function $V:\mathcal X\to\mathbb R$ bounded below, a number $\epsilon>0$ and a finite set $\mathcal X_0\subset\mathcal X$ such that the conditional expectations $E[V(X(t+1))\mid X(t)=y]=\sum_z P_{yz}V(z)$ are finite and
--   $$E[V(X(t+1))-V(X(t))\mid X(t)=y]\le-\epsilon\quad\text{if } y\notin\mathcal X_0,\qquad(3.2)$$
--   $$E[V(X(t+1))\mid X(t)=y]<\infty\quad\text{if } y\in\mathcal X_0.\qquad(3.3)$$
--
--   **Theorem 3.1.** Then $P(\tau_x<\infty)=1$ for every transient state $x\in T$, where $\tau_x$ is the first time $t>0$ the chain started at $x$ leaves $T$ (3.1), and every state of $\bigcup_j R_j$ is positive recurrent; that is, the chain is stable in the sense of Definition 3.1.
--
--   This is Foster's criterion extended to reducible chains; it is the tool that turns the quadratic drift bound for policy $\pi_0$ into stability.
--
--   **Formalization Note.** The expectation $\sum_z P_{yz}V(z)$ is a real series; its finiteness is stated as summability of $z\mapsto P_{yz}V(z)$, both in (3.3) and, implicitly on the page, in (3.2).
-- source:
--   Tassiulas and Ephremides, Stability properties of constrained queueing systems and scheduling policies for maximum throughput in multihop radio networks, IEEE Trans. Automat. Control 37(12) (1992), pp. 1938–1939, Theorem 3.1, (3.2)–(3.3)

import Mathlib
import Definitions.Def_ConstrainedQueueing_MaxThroughput_MarkovChain

open scoped ENNReal

namespace ConstrainedQueueing.MaxThroughput

/-- Theorem 3.1 (pp. 1938–1939): a lower-bounded `V` with drift `≤ -ε` off a finite set `X₀`
(3.2), and finite conditional expectation on `X₀` (3.3), makes the chain stable
(Definition 3.1). -/
theorem theorem_3_1 {σ : Type*} [Countable σ] (P : σ → σ → ℝ≥0∞) (hP : IsStochastic P)
    (V : σ → ℝ) (hV : BddBelow (Set.range V)) (ε : ℝ) (hε : 0 < ε) (X₀ : Finset σ)
    (h32 : ∀ y, y ∉ X₀ →
      Summable (fun z => (P y z).toReal * V z) ∧ (∑' z, (P y z).toReal * V z) - V y ≤ -ε)
    (h33 : ∀ y ∈ X₀, Summable (fun z => (P y z).toReal * V z)) :
    IsStable P := by sorry

end ConstrainedQueueing.MaxThroughput
