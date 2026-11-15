-- Prove2me | Theorems.Thm_FengLiYangMatching_General_Supplement_lemma_5_1
-- name    : FengLiYangMatching.General.Supplement.lemma_5_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T03:23:37.174816+00:00
-- url     : https://prove2.me/theorems/8ec2070b-8cc9-473d-af8f-6c40a618f48c
-- title:
--   Lemma 5.1 — Optimal order-model value and threshold attainment
-- statement:
--   Let $G$ be a finite simple graph, randomly labelled uniformly by all vertex bijections, and reveal its edges in an independent uniform random order without timestamps. Policies may be randomized and may know $G$ up to isomorphism. Let $W_G(P)$ be their expected final matching size, averaged over both finite random choices and the independent private seed. With $V$ defined by Equations (13)–(14),
--
--   $$V^\star(G)=V(\varnothing,[n]),\qquad W_G(P)\le V(\varnothing,[n])\quad\text{for every }P,$$
--   $$W_G(P_{\mathrm{threshold}})=V(\varnothing,[n]).$$
--
--   The threshold policy accepts a feasible arriving edge $e$ if and only if $1+V(H+e,U\setminus e)\ge V(H+e,U)$, including equality. Thus the supremum over all randomized policies is attained by the specified deterministic rule. This is the shared supporting result for Theorems 1.3 and 1.4.
--
--   Differences from the source:
--   - encoding: arbitrary finite labelled vertex set → Fin n and unordered Sym2 edges, for every natural n; reason: every finite simple graph has such a labelling; the representation removes no instance
--   - encoding: expected matching size for randomized online algorithms → lower Lebesgue integrals of ENNReal-valued finite counts with one independent uniform real seed; reason: one seed encodes private randomness; measurable policies retain their ordinary expectations and no Bochner default is used
--   - encoding: the optimal value equals the recurrence value and is attained → equality for the supremum over all randomized policies, a bound for every policy, and equality for the concrete threshold policy; reason: the universal bound makes the same optimality assertion explicit and attainment remains a separate conclusion
--   - generalization: Section 5 initially assumes OPT(G)>0 → all finite simple graphs, including the empty and zero-optimum cases; reason: the recurrence and both policy values are zero on edgeless graphs; restricting to positive optimum recovers every source instance
-- source:
--   Yilong Feng, Haolong Li, Zonghan Yang, Improved Bounds for Online Matching with Random Edge Arrivals, STOC 2027 submission #1018 (October 2026), Lemma 5.1, p. 17.

import Definitions.Def_FengLiYangMatching_General_Supplement_DynamicProgram

open MeasureTheory Finset
open scoped BigOperators ENNReal

set_option autoImplicit false

namespace FengLiYangMatching.General.Supplement

theorem lemma_5_1 {n : ℕ} (G : SimpleGraph (Fin n)) :
    optimalOrderValue G = ENNReal.ofReal (value G ∅ univ) ∧
    (∀ P : OrderPolicy n, orderValue G P ≤ ENNReal.ofReal (value G ∅ univ)) ∧
    orderValue G (thresholdPolicy G) = ENNReal.ofReal (value G ∅ univ) := by sorry

end FengLiYangMatching.General.Supplement
