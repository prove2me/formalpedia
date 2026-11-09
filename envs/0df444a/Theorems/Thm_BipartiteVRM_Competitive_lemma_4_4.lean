-- Prove2me | Theorems.Thm_BipartiteVRM_Competitive_lemma_4_4
-- name    : BipartiteVRM.Competitive.lemma_4_4
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T11:06:33.27033+00:00
-- url     : https://prove2.me/theorems/939ce9e4-06a6-402d-8031-0f6c3e995abb
-- title:
--   Lemma 4.4 — both optimal-path age bounds, for every vertex
-- statement:
--   Fix $\gamma>1$, any causal deterministic tie rule, a TA-optimal perfect matching $M^*$, and a stable time $t$. Let $r$ be a free request whose optimal path $P^*=P_r^*(t)$ ends at an already arrived server. Put $D^*=D(P^*\cap M^*)$. Then
--
--   $$D^*\ge\operatorname{age}(r,t),\qquad
--   D^*\ge\frac{\operatorname{age}(v,t)}{\gamma+1}\quad\text{for every vertex }v\text{ of }P^*.$$
--
--   Here $\operatorname{age}(v,t)=t-a_v$. The second inequality covers both endpoints and every interior vertex. Since a free request has strictly positive age at a stable time, the first inequality makes the Case 2 denominator positive. No positivity of edge distances or OPT is imposed.
--
--   Differences from the source:
--   - encoding: finite disjoint labeled sets R and S in any metric space → finite natural-number supports on the disjoint sum of two label types, Finset edges, and arbitrary MetricSpace X; reason: every finite labeled instance can be relabeled this way; labels give no future data and distinct items may coincide in space and time
--   - encoding: the RA, SA and AU execution with an arbitrary fixed tie rule → unbounded iteration of the explicit event transition with cached simple minimum paths and a fixed View-only selector over nonempty finite choices; reason: the local rule sees only received arrival times, distances and its history; the environment advances the real clock and reveals arrivals; termination and feasible completion are conclusions, not fields or hypotheses
--   - encoding: the path component of M_t symmetric-difference Mstar containing a free request → the ordered walk which follows an Mstar edge forward and an M_t edge backward, with an analysis bound of size plus one iterations; reason: optimal_path_component concludes that this computes the whole component; the terminal server need not have arrived
-- source:
--   Tung-Wei Kuo, STOC 2027 submission #528 (October 2026), p. 11, Lemma 4.4

import Definitions.Def_BipartiteVRM_Competitive_Specifications

set_option autoImplicit false

namespace BipartiteVRM.Competitive

/-- Lemma 4.4, p. 11. Includes both inequalities and every vertex of the optimal path. -/
theorem lemma_4_4 {X : Type*} [MetricSpace X] (I : Input X)
    (γ : ℝ) (hγ : 1 < γ) (tie : TieRule) (Mstar : Matching)
    (hMstar : IsOptimal I Mstar) (t : ℝ) (ht : stable I γ tie t)
    (r : ℕ) (hr : r ∈ freeAt I γ tie t) (hcase : CaseTwo I γ tie Mstar t r) :
    age I (.inl r) t ≤ optimalLength I γ tie Mstar t r ∧
      ∀ v ∈ optimalPath I γ tie Mstar t r,
        age I v t / (γ + 1) ≤ optimalLength I γ tie Mstar t r := by sorry

end BipartiteVRM.Competitive
