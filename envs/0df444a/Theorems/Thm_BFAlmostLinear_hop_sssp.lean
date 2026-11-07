-- Prove2me | Theorems.Thm_BFAlmostLinear_hop_sssp
-- name    : BFAlmostLinear.hop_sssp
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T21:41:46.597261+00:00
-- url     : https://prove2.me/theorems/8ad48d30-be86-43d1-884e-df985d68ee19
-- title:
--   §1.1 — $h$-negative hop distances in $O(h(m+n\log n))$ by the Dijkstra–Bellman-Ford hybrid
-- statement:
--   Let $G$ be a weighted directed multigraph with $n$ vertices and $m$ arcs whose unflagged arcs have non-negative weight and whose flagged ("negative") arcs have arbitrary real weight. There is a deterministic program and a constant $C>0$ such that, for every source $s$ and hop bound $h$, the program halts within
--   $$C\,(h+1)\,\big(m+n\log_2(n+2)+1\big)$$
--   steps and outputs $d^h(s,t)$ for every vertex $t$, with a flag for $d^h(s,t)=+\infty$.
--
--   This is the paper's base subroutine: it computes hop-bounded distances, and with $h=2$ it finishes the computation in the proof of Theorem 1.1.
--
--   **Formalization Note** The word bound is $(m+n+h+2)^c$. Hops are the flagged arcs, which may include arcs made non-negative by an earlier reweighting.
--
--   Differences from the source:
--   - reading: "we can compute … in $O(h(m+n\log n))$" → one deterministic program halting within $C(h+1)(m+n\log_2(n+2)+1)$ steps on the mission's machine; reason: the paper names no machine; $h+1$ and $+1$ keep $h=0$ (Dijkstra) and $m=0$ non-vacuous.
--   - generalization: hops are the arcs of negative weight → hops are any flagged set containing the arcs of negative weight; reason: the paper counts frozen arcs as hops (p.2); with flags equal to the signs it is the printed statement.
--   - encoding: "for all other $t$" → for every $t$, with an unreachability flag; reason: $d^h(s,s)$ is also output, which only adds a value.
-- source:
--   Hair, Li, Li, Zhang, Bellman-Ford in Almost-Linear Time, STOC 2027 submission (manuscript sha256 873b9acb…), §1.1, p.2 (citing [DI17])

import Mathlib
import Definitions.Def_BFAlmostLinear_flagInit

namespace BFAlmostLinear

/-- **§1.1, p.2**, the hybrid of Dijkstra and Bellman-Ford. "Given a source vertex s, we can compute d^h(s, t) for all
other t ∈ V in O(h(m + n log n)) using a hybrid of Dijkstra and Bellman-Ford [DI17]."

Hair, Li, Li, Zhang, *Bellman-Ford in Almost-Linear Time*, STOC 2027 submission (manuscript sha256
873b9acb…), §1.1, p.2.

**Formalization Note.** A deterministic program on the input `(G, flags, s, h)`, with word bound
`(m + n + h + 2)^c`. Unflagged arcs are nonnegative and flagged arcs are arbitrary. `d^h` is over real arcs, so
auxiliary arcs, if the input flags any, are ignored. The bound is
`C (h + 1) (m + n log₂(n + 2) + 1)`: `h + 1` and `+ 1` make `h = 0` (Dijkstra) and `m = 0` non-vacuous. -/
theorem hop_sssp :
    ∃ (P : Machine.Program) (C : ℝ), 0 < C ∧ Machine.NoCoin P ∧
      ∀ (n m : ℕ) (G : WGraph (Fin n) (Fin m)) (s : Fin n) (h : ℕ),
        G.Frozen →
        let W := Machine.wordBound P (m + n + h + 2)
        let σ₀ := flagInit G s h (fun _ => 0)
        let T := ⌈C * ((h : ℝ) + 1) * ((m : ℝ) + n * Real.logb 2 ((n : ℝ) + 2) + 1)⌉₊
        Machine.HaltsWithin P W Machine.zeroTape σ₀ T ∧
          IsHopOutput G h s (Machine.run P W Machine.zeroTape σ₀ T) := by sorry

end BFAlmostLinear
