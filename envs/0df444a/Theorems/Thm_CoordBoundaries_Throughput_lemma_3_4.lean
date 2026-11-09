-- Prove2me | Theorems.Thm_CoordBoundaries_Throughput_lemma_3_4
-- name    : CoordBoundaries.Throughput.lemma_3_4
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T08:49:28.630716+00:00
-- url     : https://prove2.me/theorems/5292e0d6-7820-432d-9015-973acd009ff7
-- title:
--   Lemma 3.4 — (a_j b_j)(a_k b_k) ≥ 1/16 − (3/4)(e_j + e_k) for good jobs
-- statement:
--   For good jobs $j,k$ of a feasible solution of the relaxation (global jobs with $a_j,b_j,a_k,b_k\ge 1/4$),
--   $$(a_jb_j)(a_kb_k)\ge\frac1{16}-\frac34(e_j+e_k),$$
--   where $e_j=(a_j+b_j)/4-a_jb_j$.
--
--   It converts the crossing gains of Lemma 3.2 into the deficit that Lemma 3.3 pays.
--
--   **Formalization Note** $a_j+b_j\le y_j\le 1$ comes from the job constraint of the relaxation.
--
--   Differences from the source:
--   - generalization: a feasible solution of the consistent relaxation with the density constraints → only the configuration solution (with y_j ≤ 1) is assumed; reason: the proof uses only a, b ≥ 1/4 and a + b ≤ 1
--   - generalization: the residual instance after discarding individually infeasible jobs in §2, with positive machine count and configuration cap → also permits jobs with processing time exceeding their window length, zero machines, a zero configuration cap; reason: individually infeasible jobs occur in no feasible configuration or schedule; the extra zero cases have only empty configurations or zero marginals, and every source instance is included
-- source:
--   Tong and Xu, Coordinating Boundaries: Improved Approximation Algorithms for Unweighted Non-Preemptive Throughput Maximization, preprint of October 25, 2026 (STOC 2027 submission #141; source.pdf sha256 59f76539a5ee555f9e56603a067e9f858f38d003011e90b1716085348673687e), p. 20, Lemma 3.4

import Mathlib
import Definitions.Def_CoordBoundaries_Throughput_Rounding

open Classical

namespace CoordBoundaries.Throughput

/-- **Lemma 3.4** (Tong–Xu, p. 20). For good jobs `j, k` of a feasible relaxation solution,
`(a_j b_j)(a_k b_k) ≥ 1/16 − (3/4)(e_j + e_k)`. -/
theorem lemma_3_4 {I : Instance} (hI : I.Valid) {P : Partition I.T} {K : ℕ}
    (s : ConfigSol I P K)
    (j k : Fin I.n) (hj : s.IsGood j) (hk : s.IsGood k) :
    1 / 16 - 3 / 4 * (s.e j + s.e k) ≤ (s.a j * s.b j) * (s.a k * s.b k) := by sorry

end CoordBoundaries.Throughput
