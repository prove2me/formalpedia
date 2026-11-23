-- Prove2me | Theorems.Thm_ChenCapacityTerminals_Exact_terminal_cardinality
-- name    : ChenCapacityTerminals.Exact.terminal_cardinality
-- status  : Open
-- author  : @Mr Robbins
-- created : 2026-11-23T06:21:55.136932+00:00
-- url     : https://prove2.me/theorems/257bc458-e696-46b0-8539-51da327720c7
-- title:
--   Theorem 2.1 — terminal cardinality and postorder charging
-- statement:
--   There is an absolute $C>0$ such that every legal terminal construction on a prepared rooted network, with $1\le d\le n$, $L>0$, and $t\ge1$, returns a set $P\subseteq V\setminus\{r\}$ satisfying
--
--   $$
--   |P|\le C\frac nd\log(2+m)+\frac{W}{t+1},
--   \qquad W=\sum_{v\in V}b(v).
--   $$
--
--   The first term combines the at-most-$n/d$ newly formed source probes with Lemma 2.2's greedy-cover estimate. For the second term, every strict postorder mark discards a disjoint integral-mass portion of size at least $t+1$; the dummy root has mass zero, and deleting $r$ and the dummy from the output only helps. The bound applies uniformly to all legal tie choices and does not require $L$ to be a valid cut lower bound.
-- source:
--   Thomas Chen, STOC 2027 submission #665 (October 2026), Theorem 2.1, §2.1 source probes, Lemma 2.2, and §2.3 “Weighted separation and implementation”, pp. 3–5, PDF pp. 4–7; https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/665.pdf#page=6

import Definitions.Def_ChenCapacityTerminals_Exact_Specifications

set_option autoImplicit false

open ChenCapacityTerminals.Exact

theorem ChenCapacityTerminals.Exact.terminal_cardinality :
    ∃ C : ℝ, 0 < C ∧ ∀ (G : Network) (r d : ℕ) (L : ℚ) (b : ℕ → ℕ) (t : ℕ)
      (c : Construction), Prepared G r → 1 ≤ d → d ≤ G.vertices.card → 0 < L → 1 ≤ t →
      LegalConstruction G r d L b t c →
      c.terminals G r ((L : ℝ) / (4 * d)) b t ⊆ G.vertices \ {r} ∧
      (c.terminals G r ((L : ℝ) / (4 * d)) b t).card ≤
        C * ((G.vertices.card : ℝ) / d) * Real.log (2 + (G.arcs.length : ℝ)) +
          (mass b G.vertices : ℝ) / (t + 1 : ℕ) := by sorry
