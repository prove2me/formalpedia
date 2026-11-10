-- Prove2me | Theorems.Thm_FlowOptimalSeparators_MinorFree_expected_path_weight
-- name    : FlowOptimalSeparators.MinorFree.expected_path_weight
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-10T00:07:01.961002+00:00
-- url     : https://prove2.me/theorems/6260ff16-3882-443c-9341-a15bdc9ad88a
-- title:
--   Lemma 1 — connector path expectation and tree radius
-- statement:
--   Let $C=(X,r,B)$ be a wide connector with load $p_C$, and let $\widetilde w$ be any nonnegative vertex weight vector. Choose $b$ uniformly in $B$ and let $Q=X[r,b]$, including both endpoints. If $D_X$ is the maximum full vertex-weight sum of a root path in the tree $X$, then
--   $$\mathbb E[\widetilde w(Q)]=\sum_v\widetilde w(v)p_C(v)\le D_X.$$
--   Both the identity and the radius bound are retained. The radius belongs to the connector's tree, rather than the ambient graph, and the finite expectation has no integrability default.
--
--   Differences from the source:
--   - encoding: finite undirected simple graphs on arbitrary vertex sets → SimpleGraph (Fin n), with arbitrary duplicate-free adjacency-list orders; reason: vertex relabelling preserves all graph notions and CSR arrays have linear input size
--   - reading: exactly 3n/4 terminals; line 10 chooses them outside the root → ceil(3n/4) terminals, excluding the root whenever enough other cluster vertices exist; reason: the printed count is undefined off multiples of four; at n=401 a 301-vertex cluster needs the root to reach 301 terminals; this agrees with the source when four divides n
--   - encoding: uniform-terminal expectation and the tree radius D → a finite average and the maximum over the finite nonempty tree vertex set; reason: these are exactly the expectation and radius; the root ensures nonemptiness
-- source:
--   Hung Le, Jack Spalding-Jamieson, STOC 2027 submission #1211 (October 2026), p. 13, Lemma 1, Eq. (17)

import Mathlib
import Definitions.Def_FlowOptimalSeparators_MinorFree_Connectors

set_option autoImplicit false

namespace FlowOptimalSeparators.MinorFree

/-- Lemma 1, p.13, (17): both the finite expectation identity and the tree-radius bound.
Paths are the tree's parent paths, with both endpoints included. -/
theorem expected_path_weight {n : ℕ} (G : Graph n) (C : WideConnector G)
    (w : Fin n → ℝ) (hw : ∀ v, 0 ≤ w v) :
    pathExpectation C w = ∑ v, w v * load C v ∧
    (∑ v, w v * load C v) ≤ treeRadius C w := by sorry

end FlowOptimalSeparators.MinorFree
