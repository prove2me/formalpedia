-- Prove2me | Theorems.Thm_FlowOptimalSeparators_MinorFree_connector_progress
-- name    : FlowOptimalSeparators.MinorFree.connector_progress
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-10T00:08:11.239978+00:00
-- url     : https://prove2.me/theorems/1935c883-9327-4521-9937-28709c9f5b60
-- title:
--   Lemma 2 — Cluster-FTRL progress
-- statement:
--   Consider Algorithm 2 with $h\ge2$, a graph excluding the once-subdivided $K_h$ as an induced minor, $D>0$, and $\mu,\iota\ge0$. Suppose it completes $T$ connector-producing rounds, with the source's fresh roots and ceiling-weight shortest-path trees. Let $\overline\lambda$ be the indicator of its returned connectors, regarded as a vector over every connector in the graph. Then
--   $$\overline\lambda\text{ is feasible},\qquad F_{\mu,\iota}(\overline\lambda)\ge\frac{3T}{4}.$$
--   The prefix relation contains the preceding transitions, not a congestion or progress assumption. Distinct roots and both clauses of the conclusion are preserved.
--
--   Differences from the source:
--   - encoding: finite undirected simple graphs on arbitrary vertex sets → SimpleGraph (Fin n), with arbitrary duplicate-free adjacency-list orders; reason: vertex relabelling preserves all graph notions and CSR arrays have linear input size
--   - reading: exactly 3n/4 terminals; line 10 chooses them outside the root → ceil(3n/4) terminals, excluding the root whenever enough other cluster vertices exist; reason: the printed count is undefined off multiples of four; at n=401 a 301-vertex cluster needs the root to reach 301 terminals; this agrees with the source when four divides n
--   - encoding: the regularization n deg(v)/(2m) in an attempted FTRL round → 0 < m for the FTRL-round lemmas; reason: this excludes only division by zero in the source formula; zero-edge and empty inputs remain covered by the goal and need no FTRL rounds
--   - generalization: Algorithm 2 returns its connector set after T rounds → a length-T list satisfying each connector-producing source transition, and its set indicator; reason: all actual runs are included; the proof uses only legal cluster outcomes, fresh roots and shortest-tree paths, so the claim also covers every legal such transition sequence
-- source:
--   Hung Le, Jack Spalding-Jamieson, STOC 2027 submission #1211 (October 2026), p. 15–16, Lemma 2, Eqs. (20)–(21)

import Mathlib
import Definitions.Def_FlowOptimalSeparators_MinorFree_FTRLTrace

set_option autoImplicit false

namespace FlowOptimalSeparators.MinorFree

/-- Lemma 2, p.15, (20)-(21): all allowable fresh-root/shortest-tree choices of Algorithm 2.
The indicator ranges over every connector in the graph. -/
theorem connector_progress {n : ℕ} (G : Graph n) (h : ℕ) (hh : 2 ≤ h)
    (hG : InducedSubdivisionFree G h) (hm : 0 < edgeCount G) (D μ ι : ℝ) (hD : 0 < D)
    (hμ : 0 ≤ μ) (hι : 0 ≤ ι) (T : ℕ) (Cs : List (WideConnector G))
    (hT : Cs.length = T) (hrun : IsFTRLPrefix G D μ ι Cs) :
    Feasible (connectorIndicator Cs) ∧
      3 * (T : ℝ) / 4 ≤ objective G μ ι (connectorIndicator Cs) := by sorry

end FlowOptimalSeparators.MinorFree
