-- Prove2me | Theorems.Thm_CostlySeeding_EdgeQuery_worst_case_queries
-- name    : CostlySeeding.EdgeQuery.worst_case_queries
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-21T00:27:39.857543+00:00
-- url     : https://prove2.me/theorems/5dd78351-91e2-4545-aa8a-d2869ca474c8
-- title:
--   B.12, p. 46 — worst-case query count
-- statement:
--   For any initial vertex set, any threshold, and every realization of the $T$ PROBE copies on a graph with $n$ vertices, the total query count satisfies
--
--   $$
--   q\le2Tn^2.
--   $$
--
--   This coarse worst-case bound controls the query count on the exceptional event in the expectation bound (30). It counts both first-chance and discarded second-chance queries.
-- source:
--   Eckles, Esfandiari, Mossel & Rahimian, Seeding with Costly Network Information, arXiv:1905.04325v5, p. 46, B.12 paragraph after (30)

import Definitions.Def_CostlySeeding_EdgeQuery_Algorithm

namespace CostlySeeding.EdgeQuery

theorem worst_case_queries (n T tau : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (Vrho : Finset (Fin n)) (ss : Fin T → ProbeSeed n) :
    queries G Vrho tau ss ≤ 2 * T * n ^ 2 := by sorry

end CostlySeeding.EdgeQuery
