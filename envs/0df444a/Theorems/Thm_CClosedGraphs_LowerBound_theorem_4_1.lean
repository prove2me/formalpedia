-- Prove2me | Theorems.Thm_CClosedGraphs_LowerBound_theorem_4_1
-- name    : CClosedGraphs.LowerBound.theorem_4_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T21:22:30.159278+00:00
-- url     : https://prove2.me/theorems/3ac68e8c-4024-442d-b9d6-7b713b99c2df
-- title:
--   Theorem 4.1, p. 12 — for c ≥ 2 and n ≥ c there are c-closed graphs on n vertices with Ω(c^{−3/2} 2^{c/2} n^{3/2}) maximal cliques
-- statement:
--   There is an absolute constant $C > 0$ with the following property. For all integers $c \ge 2$ and $n \ge c$ there is a $c$-closed graph $G$ on $n$ vertices whose number of maximal cliques satisfies
--   $$
--   \#\mathrm{MC}(G) \ \ge\ C\, c^{-3/2}\, 2^{c/2}\, n^{3/2} .
--   $$
--
--   This is the lower-bound half of the paper's results on maximal cliques in $c$-closed graphs: the exponent of $n$ in the upper bounds cannot be pushed below $3/2$, and the dependence on $c$ must be at least exponential in $c/2$.
--
--   **Formalization Note** The constant hidden in the paper's $\Omega$ is absolute, so $C$ is quantified before $c$ and $n$; the dependence on $c$ is explicit. The paper states the theorem "for any positive integer $c$"; two hypotheses are added because the printed statement is false without them: (1) $c \ge 2$, since a $1$-closed graph is a disjoint union of cliques and has at most $n$ maximal cliques; (2) $n \ge c$, since any graph on $n$ vertices has at most $3^{n/3}$ maximal cliques (Moon–Moser), which is below $c^{-3/2} 2^{c/2} n^{3/2}$ when $n$ is small compared with $c$. The construction itself assumes $n$ is a positive multiple of $c$. The paper's reduction to even $c$ and $c \mid n$ ("with only an absolute constant factor loss") is part of the proof and is not a hypothesis. Powers are real powers.
-- source:
--   Fox, Roughgarden, Seshadhri, Wei and Wein, Finding cliques in social networks: a new distribution-free model, arXiv:1804.07431v1, p. 12, Theorem 4.1 (restatement of Theorem 1.7, p. 4)

import Mathlib
import Definitions.Def_CClosedGraphs_LowerBound_Setting

namespace CClosedGraphs.LowerBound
theorem theorem_4_1 : ∃ C : ℝ, 0 < C ∧ ∀ c n : ℕ, 2 ≤ c → c ≤ n →
    ∃ G : SimpleGraph (Fin n), CClosedGraphs.Peeling.IsCClosed c G ∧
      C * (c : ℝ) ^ (-(3 : ℝ) / 2) * (2 : ℝ) ^ ((c : ℝ) / 2) * (n : ℝ) ^ ((3 : ℝ) / 2)
        ≤ (CClosedGraphs.Peeling.numMaxCliques G : ℝ) := by sorry
end CClosedGraphs.LowerBound
