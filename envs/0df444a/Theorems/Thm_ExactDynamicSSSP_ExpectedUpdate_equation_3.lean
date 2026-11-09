-- Prove2me | Theorems.Thm_ExactDynamicSSSP_ExpectedUpdate_equation_3
-- name    : ExactDynamicSSSP.ExpectedUpdate.equation_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T09:32:48.914105+00:00
-- url     : https://prove2.me/theorems/6adc8758-ab9f-45ab-a4f4-c66906901098
-- title:
--   Section 5, equation (3) — actual work per update is O(1 + m′ + n′ log(2 + n′))
-- statement:
--   There is an absolute constant $K$ such that, for every graph with arbitrary nonnegative real weights, every reachable state of the data structure and every update request (insertion, deletion, weight decrease or increase),
--   $$T\le K\bigl(1+m'+n'\log(2+n')\bigr),$$
--   where $T$ is the actual work of that execution (including all heap work, boundary scans, internal relaxations, list and certificate operations, marking and parent reattachment, and the initial record modification), $n'=|V'|$ is the number of processed vertices and $m'=|E'|$ the number of distinct scanned arcs of the same execution.
--
--   This is the deterministic local-work bound used by the probabilistic analysis.
--
--   Differences from the source:
--   - reading: T = the update time of the implementation of Section 5 (unit-cost real additions/comparisons and pointer/record operations) → T = updateWork: the charged execution of Algorithm 1, Algorithm 3 and the indexed Fibonacci heap in the source pointer-operation model; reason: the source fixes the pointer implementation and unit-cost model but no charge table; the definition counts constant-size groups of its primitive operations, with scans, cuts, links and table visits charged explicitly
--   - reading: weight updates are decreases or increases → a weight change to an equal weight is processed by Algorithm 1 (record change only); reason: the source does not treat w' = w; in the random model it has probability 0
--   - encoding: n′, m′: processed vertices and distinct scanned edges → the sets V′, E′ returned by the instrumented execution; E′ excludes the initially modified record, whose constant work is in the leading 1; reason: §6.6: 'the initial constant-time modification is accounted for separately'
--   - encoding: indexed edge and heap handles, adjacency lists, tree-child links, cached degrees and preferred incoming-record minima in the pointer-operation cost model → maps and lists specify pointer-structure contents extensionally; the cost counts their source operations, and processed/scanned sets are ghost observations; reason: map updates denote handle writes, erase denotes unlinking a known handle, adjacency and subtree enumerations charge their visited entries, and heap scans/links/promotions are charged explicitly; costs describe the source pointer program, not evaluation of the functional Lean representation
--   - generalization: valid single-edge updates → all update requests, with invalid requests ignored at work 1; reason: every source update is valid and runs the source procedure; the extra invalid cases satisfy the same bound by the constant term
--   - encoding: finite directed graphs with finite nonnegative real arc weights and shortest-path distances → vertices Fin n, absent arcs none and present weights in ℝ≥0; exact distances are ℝ≥0∞ infima of walk weights; reason: bijective relabeling represents every finite vertex set; Option distinguishes absent arcs; deleting cycles from nonnegative walks gives the same shortest-path minimum, with ∞ for unreachable vertices
-- source:
--   Jun Liang, Yuhan Chen, Zanbo Zhang, STOC 2027 submission #223 (October 2026), https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/223.pdf (source.pdf sha256 69de237b275cb22a0d01b1d683efc6477bccb039ca7a2f867f7c6785a9c71d50), Section 5, 'Per-update bound', equation (3), PDF p.7 = printed p.7; Appendix B.1, PDF p.16

import Mathlib
import Definitions.Def_ExactDynamicSSSP_ExpectedUpdate_Algorithm

open scoped ENNReal NNReal

namespace ExactDynamicSSSP.ExpectedUpdate

/-- Section 5, equation (3) (PDF p. 7). There is an absolute constant `K` such that every update
request, in either direction, applied to any state of the data structure, has actual work at
most `K (1 + m' + n' log(2 + n'))`, where `n' = |V'|` is the number of processed vertices and
`m' = |E'|` the number of distinct scanned arcs of that execution. -/
theorem equation_3 :
    ∃ K : ℝ, 0 < K ∧ ∀ (n : ℕ) (G : WDigraph n) (s : Fin n) (ds : DS n),
      IsReachableState G s ds → ∀ upd : Update n,
        ((applyUpdate ds upd).cost : ℝ) ≤
          K * (1 + ((applyUpdate ds upd).scanned.card : ℝ) +
            ((applyUpdate ds upd).processed.card : ℝ) *
              Real.log (2 + ((applyUpdate ds upd).processed.card : ℝ))) := by sorry

end ExactDynamicSSSP.ExpectedUpdate
