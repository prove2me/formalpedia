-- Prove2me | Theorems.Thm_BatchMaxService_Metric_Supplement_subtree_twelve_competitive
-- name    : BatchMaxService.Metric.Supplement.subtree_twelve_competitive
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T16:06:14.427811+00:00
-- url     : https://prove2.me/theorems/d3a83d2a-b3c1-403d-9f54-4da0063f5b16
-- title:
--   Theorem 5.4 — Algorithm 2 is deterministic, polynomial-time and 12-competitive
-- statement:
--   On every finite represented positive-weight tree in its vertex path metric, Algorithm 2 is deterministic and nonanticipating, terminates on every finite visible input, and runs in polynomial arithmetic/comparison work under either elective or automatic service. In particular, for each service rule $r$,
--
--   $$\operatorname{cost}(\operatorname{Algorithm2}_r(I))\le12\operatorname{OPT}_r(I).$$
--
--   Polynomial work is uniform: there are positive natural $C$ and a natural degree $d$, chosen before the tree size, metric, rule and input, bounding the operational counter by $C(Q+N+1)^d$. Waiting is not computational work. A one-vertex tree, real edge lengths and arrival times, empty input and repeated request locations are included. This supplies the tree companion theorem rather than an assumed approximation certificate.
--
--   Differences from the source:
--   - encoding: known finite metrics, distinct requests and real arrival times → enumerated sites Fin n, natural identity labels and unrestricted real arrival times; reason: enumeration preserves every finite metric and repeated location/time pairs; a specified start already excludes the empty carrier
--   - encoding: deterministic online execution under the stated feedback → functional feedback callbacks with interruptible timers and a terminating feasible interaction; reason: the callbacks cannot inspect future input or undiscovered locations; finite evaluator fuel does not limit a policy
--   - encoding: explicitly represented finite tree with positive edge weights and polynomial running time → published metric-tree edge data with path-metric compatibility and a uniform unit-cost real arithmetic/comparison work polynomial; reason: positive tree edges are distances of distinct vertices; all such weighted trees are represented, and the counter charges operational scans and traversals rather than elapsed waiting
-- source:
--   Lu, Ren, Liu, Tang, Online Service with Per-Batch Maximum Delays, STOC 2027 submission #218 (October 2026), canonical source.pdf sha256 652f1a7bbf08e31c9fd0855a098b7b7439589f55b2df3115db7c34adc0eaec34, Theorem 5.4, printed p. 16 / PDF p. 17

import Mathlib
import Definitions.Def_BatchMaxService_Metric_Supplement_Visible

namespace BatchMaxService.Metric.Supplement

theorem subtree_twelve_competitive :
    PolynomialAlgorithm2Work ∧
    ∀ {n : ℕ} [MetricSpace (Fin n)] (T : MetricTree n), IsWeightedTree T →
      ∀ r : Rule,
      (∀ I : RequestInput n, ValidOn .visible r (treePolicy (minimalSubtree T)) I) ∧
      (∀ I J : RequestInput n, ∀ t : ℝ, 0 ≤ t → SameHistory I J t →
        logThrough t (algorithm2 T r I).log = logThrough t (algorithm2 T r J).log) ∧
      ∀ I : RequestInput n,
        ENNReal.ofReal (cost I (algorithm2 T r I).log) ≤ 12 * ruleOPT r I := by sorry

end BatchMaxService.Metric.Supplement
