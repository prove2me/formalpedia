-- Prove2me | Theorems.Thm_BipartiteVRM_Competitive_lemma_3_3
-- name    : BipartiteVRM.Competitive.lemma_3_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T11:07:13.21806+00:00
-- url     : https://prove2.me/theorems/4b8b8662-d6b9-4c6c-a88c-a6b7239b564b
-- title:
--   Lemma 3.3 — no free request is ready at a stable time
-- statement:
--   Fix $\gamma>1$, any causal deterministic tie rule, and a stable time $t\ge0$, when no arrival or augmentation occurs. For every free request $r$, its minimum net cost satisfies $\varphi_r>\gamma(t-a_r)$. Every augmenting path $P$ from $r$ to a free server in the arrived graph therefore satisfies
--
--   $$\varphi_{M_t}(P)\ge\varphi_r>\gamma(t-a_r).$$
--
--   The no-readiness conclusion is asserted even when there is no free server, in which case $\varphi_r=+\infty$. This supplies the waiting inequality used in the optimal-path estimates. It makes no strict-readiness claim at event boundaries.
--
--   Differences from the source:
--   - encoding: finite disjoint labeled sets R and S in any metric space → finite natural-number supports on the disjoint sum of two label types, Finset edges, and arbitrary MetricSpace X; reason: every finite labeled instance can be relabeled this way; labels give no future data and distinct items may coincide in space and time
--   - encoding: the RA, SA and AU execution with an arbitrary fixed tie rule → unbounded iteration of the explicit event transition with cached simple minimum paths and a fixed View-only selector over nonempty finite choices; reason: the local rule sees only received arrival times, distances and its history; the environment advances the real clock and reveals arrivals; termination and feasible completion are conclusions, not fields or hypotheses
--   - encoding: augmenting paths and a minimum net cost, with infinity if none exists → simple ordered vertex lists, their finite edge sets and a WithTop real minimum, using top on the empty path set; reason: simple paths suffice by Lemma 3.1, negative weights remain signed, and finite enumeration has no unbounded-infimum default
-- source:
--   Tung-Wei Kuo, STOC 2027 submission #528 (October 2026), p. 9, Lemma 3.3; p. 8, Definition 3.2

import Definitions.Def_BipartiteVRM_Competitive_Specifications

set_option autoImplicit false

namespace BipartiteVRM.Competitive

/-- Lemma 3.3, p. 9. The no-readiness clause also applies when no free server exists
(the minimum is then +∞), rather than disappearing into a universal over no paths. -/
theorem lemma_3_3 {X : Type*} [MetricSpace X] (I : Input X)
    (γ : ℝ) (hγ : 1 < γ) (tie : TieRule) (t : ℝ) (ht : stable I γ tie t) :
    ∀ r ∈ freeAt I γ tie t,
      (γ * age I (.inl r) t : WithTop ℝ) <
        minNetCost (I.arrived t) (edgeDistance I) γ (stateAt I γ tie t).off r ∧
      ∀ P, Augmenting (I.arrived t) (stateAt I γ tie t).off r P →
        minNetCost (I.arrived t) (edgeDistance I) γ (stateAt I γ tie t).off r ≤
          (netCost (edgeDistance I) γ (stateAt I γ tie t).off P : WithTop ℝ) := by sorry

end BipartiteVRM.Competitive
