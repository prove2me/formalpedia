-- Prove2me | Theorems.Thm_BFAlmostLinear_lemma_1_2
-- name    : BFAlmostLinear.lemma_1_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T21:42:42.714796+00:00
-- url     : https://prove2.me/theorems/a3bb3af0-3cd4-4d6a-93ee-0fc475040b12
-- title:
--   Lemma 1.2 — linear-time preprocessing to one negative arc per vertex
-- statement:
--   Let $G=(V,E)$ be a directed multigraph with $n$ vertices, $m$ arcs, real weights and $k$ negative vertices. There is a deterministic program and a constant $C$ such that on every such input the program halts within $C(m+n+1)$ steps with an output graph $G'=(V',E')$, $V'\supseteq V$, such that
--
--   1. $d^h_{G'}(s,t)=d^h_G(s,t)$ for all $s,t\in V$ and every hop bound $h$;
--   2. every vertex of $G'$ is incident to at most one negative arc; the tail of a negative arc has no other outgoing arc and its head no other incoming arc;
--   3. $G'$ has $k$ negative vertices and $|V'|=|V|+2k$.
--
--   This preprocessing puts the input into invariant (I1), which all later steps assume.
--
--   **Formalization Note** The program runs on the word/real RAM of the mission with word bound $(m+n+2)^c$ and no coin; "linear time" is $C(m+n+1)$ steps, the $+1$ covering $n=m=0$.
--
--   Differences from the source:
--   - reading: "a linear-time algorithm" → a deterministic program on the mission's word/real RAM halting within $C(m+n+1)$ steps; reason: the paper names no machine (`paper.md` decision 2).
--   - encoding: $V'\supseteq V$, $|V'|=|V|+2k$ → $V'=\{0,\dots,n+2k-1\}$ with $V$ its first $n$ vertices; reason: same graphs, the inclusion is built into the type.
--   - encoding: "negative edge" → arc of negative weight, in $G$ and in $G'$; reason: the input carries no frozen flags.
-- source:
--   Hair, Li, Li, Zhang, Bellman-Ford in Almost-Linear Time, STOC 2027 submission (manuscript sha256 873b9acb…), Lemma 1.2, p.2

import Mathlib
import Definitions.Def_BFAlmostLinear_IsPreprocessOutput

namespace BFAlmostLinear

open AtomicDynRouting.ResidenceTime

/-- **Lemma 1.2**, p.2. "Given a graph G = (V, E) with k negative vertices, there is a linear-time algorithm that
outputs a graph G′ = (V′, E′) with V′ ⊇ V" such that (1) `d^h_{G′}(s, t) = d^h_G(s, t)` for `s, t ∈ V` and every hop
bound, (2) every vertex is adjacent to at most one negative edge, which is the only outgoing edge of its tail
and the only incoming edge of its head, and (3) `G′` has `k` negative vertices and `|V′| = |V| + 2k`.

Hair, Li, Li, Zhang, *Bellman-Ford in Almost-Linear Time*, STOC 2027 submission (manuscript sha256
873b9acb…), Lemma 1.2, p.2.

**Formalization Note.** The program is deterministic, with word bound `(m + n + 2)^c`. Linear time is
`C (m + n + 1)` steps; the `+ 1` covers `n = m = 0`. Cell `2` of the input is `0`, since there is no source. -/
theorem lemma_1_2 :
    ∃ (P : Machine.Program) (C : ℕ), Machine.NoCoin P ∧
      ∀ (n m : ℕ) (G : Network (Fin n) (Fin m)) (w : Fin m → ℝ),
        let W := Machine.wordBound P (m + n + 2)
        let σ₀ := ssspInit G w 0
        let T := C * (m + n + 1)
        Machine.HaltsWithin P W Machine.zeroTape σ₀ T ∧
          IsPreprocessOutput G w (Machine.run P W Machine.zeroTape σ₀ T) := by sorry

end BFAlmostLinear
