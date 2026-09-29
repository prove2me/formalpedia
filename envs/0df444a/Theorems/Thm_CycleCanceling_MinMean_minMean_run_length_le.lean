-- Prove2me | Theorems.Thm_CycleCanceling_MinMean_minMean_run_length_le
-- name    : CycleCanceling.MinMean.minMean_run_length_le
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-26T21:15:42.190349+00:00
-- url     : https://prove2.me/theorems/57904148-e4aa-4438-b606-48df7a6fe5f9
-- title:
--   Theorem 3.9 — minimum-mean cycle canceling terminates after at most $n m^2 \lceil \ln n + 1\rceil$ iterations
-- statement:
--   Let $G=(V,E)$ be a circulation network with $n=|V|\ge 2$ vertices and $m=|E|$ arcs, with arbitrary real capacities and arbitrary real antisymmetric costs. Then every run of the minimum-mean cycle-canceling algorithm, from any starting circulation and under any tie-breaking among minimum-mean cycles, has at most
--   $$
--   K\le n\,m^2\,\bigl\lceil \ln n+1\bigr\rceil
--   $$
--   iterations.
--
--   This is the paper's main result: the classical cycle-canceling algorithm of Klein, with the minimum-mean selection rule, is strongly polynomial, in contrast with arbitrary cycle selection, which can take exponentially many iterations or fail to terminate on irrational data.
--
--   **Formalization Note** The paper prints $O(nm^2\log n)$. Its proof divides the iterations into groups of $k=m\,n\lceil\ln n+1\rceil$ consecutive iterations and shows that each group followed by a further iteration fixes the flow on a distinct arc, so there are at most $m$ such groups; this gives the explicit bound $m\cdot k$ stated here, with the natural logarithm. The hypothesis $n\ge2$ is the paper's standing assumption; its other standing assumption $m\ge n$ is not used by the proof and is omitted, which makes the statement stronger. "Terminates after at most $B$ iterations" is formalized as: every run of the algorithm has length at most $B$.
-- source:
--   Goldberg, Tarjan, Finding Minimum-Cost Circulations by Canceling Negative Cycles, J. ACM 36(4), 1989, p. 879, Theorem 3.9 (proof pp. 879-880); standing assumption n ≥ 2 on p. 874

import Mathlib
import Definitions.Def_CycleCanceling_MinMean_Network
import Definitions.Def_CycleCanceling_MinMean_Algorithm

namespace CycleCanceling.MinMean

/-- Theorem 3.9 (p. 879): for arbitrary real-valued arc costs, the minimum-mean cycle-canceling
algorithm terminates after `O(nm² log n)` iterations. Stated with the bound given by the proof
(groups of `k = m·n·⌈ln n + 1⌉` iterations, each fixing a distinct arc): every run has at most
`n · m² · ⌈ln n + 1⌉` iterations, where `n = |V| ≥ 2` and `m = |E|`. -/
theorem minMean_run_length_le {V : Type*} [Fintype V] [DecidableEq V]
    (N : CircNetwork V) (hn : 2 ≤ Fintype.card V)
    (F : ℕ → V → V → ℝ) (K : ℕ) (hrun : IsMinMeanRun N F K) :
    K ≤ Fintype.card V * N.E.card ^ 2 * ⌈Real.log (Fintype.card V) + 1⌉₊ := by sorry

end CycleCanceling.MinMean
