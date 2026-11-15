-- Prove2me | Theorems.Thm_BMPV1173_Verification_Supplement_theorem_1_3
-- name    : BMPV1173.Verification.Supplement.theorem_1_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T05:53:09.314858+00:00
-- url     : https://prove2.me/theorems/3c0a097a-2325-4de8-a8e0-3e087bd28320
-- title:
--   Theorem 1.3 — Both diameter-at-most-two query bounds
-- statement:
--   Let $G$ range over all simple unweighted undirected graphs with $n$ vertices, including disconnected graphs, under adjacency-bit access. The decision problem asks whether every two vertices are at distance at most two. Then
--
--   $$Q(\mathrm{DIAM}_{\le2,n})=\widetilde O(n^{17/12})\quad\text{and}\quad Q(\mathrm{DIAM}_{\le2,n})=\Omega(n^{5/4}).$$
--
--   The upper bound alone suppresses polylogarithmic factors. The lower bound is ordinary, and both use worst-case success at least $2/3$. The conjunction records the full separation bounds for this graph predicate.
--
--   Differences from the source:
--   - encoding: indices in [n] and bounded-error individual-entry query complexity → Fin n and the published XOR-bit HasDecision/queryComplexity interfaces with success at least 2/3; reason: a bijective relabeling of all input bits; the operational model is unchanged
--   - encoding: ordinary O and Omega notation → existential positive coefficients and dimension thresholds before n; upper bounds supply circuits and lower bounds quantify every successful circuit; reason: expands the asymptotic notation without logarithmic losses or instance-dependent constants
--   - encoding: soft-O notation → the published SoftDecisionBound with a fixed natural logarithmic exponent and coefficient before n; reason: suppresses only polylogarithmic factors and retains all input instances
--   - encoding: diameter at most two, with infinite distance between disconnected vertices → every pair satisfies equality, adjacency, or a two-edge walk on the published simple-graph domain; reason: the distance-two characterization is equivalent on every input graph and needs no finite default for infinity
--   - encoding: the graph oracle supplies off-diagonal adjacency entries, with symmetry promised → the published full matrix index has symmetric entries and fixed false diagonal entries; reason: the extra diagonal answers are input-independent constants; coherent simulation preserves the query bounds and adds no unknown graph bits
-- source:
--   Amin Shiraz Gilani, François Le Gall, Xingyu Zhou, STOC 2027 submission #1173 (October 2026), https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/1173.pdf, Theorem 1.3, printed p.4 = PDF p.4.

import Definitions.Def_BMPV1173_Verification_Supplement_Asymptotics
import Definitions.Def_BMPV1173_Verification_Supplement_Problems

namespace BMPV1173.Verification.Supplement

/-- Theorem 1.3, printed/PDF p.4: both bounds on all simple graphs. -/
theorem theorem_1_3 :
    SoftDecisionBound MatrixIndex (fun _ => {x | SimpleGraphInput x})
      (fun _ => diamTwo) (17 / 12 : ℝ) ∧
    OrdinaryDecisionLower MatrixIndex (fun _ => {x | SimpleGraphInput x})
      (fun _ => diamTwo) (powerRate (5 / 4 : ℝ)) 2 := by sorry

end BMPV1173.Verification.Supplement
