-- Prove2me | Theorems.Thm_BMPV1173_Verification_Supplement_theorem_1_4
-- name    : BMPV1173.Verification.Supplement.theorem_1_4
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T05:53:41.783053+00:00
-- url     : https://prove2.me/theorems/efec77f1-06bf-4eb6-b711-24c566d3fd07
-- title:
--   Theorem 1.4 — Both radius-at-most-two query bounds
-- statement:
--   Let $G$ range over all simple unweighted undirected $n$-vertex graphs under adjacency-bit access. Radius at most two means that some vertex is within distance two of every vertex. The full quantitative form supplied by Corollary 5.5 is
--
--   $$\Omega\!\left(\frac{n^{3/2}}{\sqrt{\log n}}\right)\le Q(\mathrm{RAD}_{\le2,n})=O(n^{3/2}),\qquad n\ge27.$$
--
--   In particular this is the $\widetilde\Theta(n^{3/2})$ statement of Theorem 1.4. Both bounds use success at least $2/3$; the upper bound has no suppressed logarithms. The two clauses pin down the source's radius bound rather than retaining only one side.
--
--   Differences from the source:
--   - encoding: indices in [n] and bounded-error individual-entry query complexity → Fin n and the published XOR-bit HasDecision/queryComplexity interfaces with success at least 2/3; reason: a bijective relabeling of all input bits; the operational model is unchanged
--   - encoding: ordinary O and Omega notation → existential positive coefficients and dimension thresholds before n; upper bounds supply circuits and lower bounds quantify every successful circuit; reason: expands the asymptotic notation without logarithmic losses or instance-dependent constants
--   - encoding: soft-Theta(n^(3/2)) in Theorem 1.4, with the explicit bounds and n>=27 in Corollary 5.5 → ordinary O(n^(3/2)) and ordinary Omega(n^(3/2)/sqrt(log n)) with dimension minimum 27; reason: uses the precise quantitative content of the source result on p.37, which entails both sides of its introductory soft-Theta statement
--   - encoding: radius at most two on possibly disconnected graphs → there exists a vertex satisfying equality, adjacency, or a two-edge walk to every vertex; reason: the distance-two predicate preserves the infinite-distance convention without imposing connectedness
--   - encoding: the graph oracle supplies off-diagonal adjacency entries, with symmetry promised → the published full matrix index has symmetric entries and fixed false diagonal entries; reason: the extra diagonal answers are input-independent constants; coherent simulation preserves the query bounds and adds no unknown graph bits
--   - encoding: n^(3/2)/sqrt(log n), with an unspecified fixed logarithm base → rowLowerRate uses Real.log, the natural logarithm; reason: changing a fixed logarithm base above one multiplies the rate by a positive constant absorbed into the existential lower-bound coefficient
-- source:
--   Amin Shiraz Gilani, François Le Gall, Xingyu Zhou, STOC 2027 submission #1173 (October 2026), https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/1173.pdf, Theorem 1.4, printed p.4 = PDF p.4. Explicit bounds: Corollary 5.5, printed p.37 = PDF p.37.

import Definitions.Def_BMPV1173_Verification_Supplement_Asymptotics
import Definitions.Def_BMPV1173_Verification_Supplement_Problems

namespace BMPV1173.Verification.Supplement

/-- Theorem 1.4, p.4, with its explicit quantitative content from Corollary 5.5, p.37. -/
theorem theorem_1_4 :
    OrdinaryDecisionUpper MatrixIndex (fun _ => {x | SimpleGraphInput x})
      (fun _ => radTwo) (powerRate (3 / 2 : ℝ)) 27 ∧
    OrdinaryDecisionLower MatrixIndex (fun _ => {x | SimpleGraphInput x})
      (fun _ => radTwo) rowLowerRate 27 := by sorry

end BMPV1173.Verification.Supplement
