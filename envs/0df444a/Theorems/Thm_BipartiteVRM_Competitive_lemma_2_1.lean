-- Prove2me | Theorems.Thm_BipartiteVRM_Competitive_lemma_2_1
-- name    : BipartiteVRM.Competitive.lemma_2_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T11:07:20.337483+00:00
-- url     : https://prove2.me/theorems/e7fd9d58-a8a8-4d1f-aff0-492e72549108
-- title:
--   Lemma 2.1 — the offline optimum equals minimum TA matching cost
-- statement:
--   Let $M^*$ be any minimum-cost perfect matching between the request and server sets under the time-augmented distance $D$. The minimum feasible timed offline cost satisfies
--
--   $$\mathrm{OPT}=D(M^*).$$
--
--   The left side is independently defined by the actual distance-plus-waiting objective (2.1), and the right side is the TA edge sum. This identifies the comparison value used in the charging analysis, without defining the benchmark to equal the expression to be proved. No VRM execution or positivity of the optimum is assumed.
--
--   Differences from the source:
--   - encoding: finite disjoint labeled sets R and S in any metric space → finite natural-number supports on the disjoint sum of two label types, Finset edges, and arbitrary MetricSpace X; reason: every finite labeled instance can be relabeled this way; labels give no future data and distinct items may coincide in space and time
--   - encoding: the minimum actual distance-plus-both-sides-delay objective OPT in (2.1) → the real projection of its ENNReal infimum over every perfect matching and feasible real match-time function; reason: offline_attainment and the main goal conclude finiteness and attainment, so the projection never substitutes a default for an infinite value
-- source:
--   Tung-Wei Kuo, STOC 2027 submission #528 (October 2026), p. 6, Lemma 2.1 ([AJF20]), equations (2.1)–(2.2)

import Definitions.Def_BipartiteVRM_Competitive_Specifications

set_option autoImplicit false

namespace BipartiteVRM.Competitive

/-- Lemma 2.1, p. 6, attributed to [AJF20]. OPT is defined by (2.1), not by this identity. -/
theorem lemma_2_1 {X : Type*} [MetricSpace X] (I : Input X)
    (Mstar : Matching) (hMstar : IsOptimal I Mstar) :
    OPT I = matchingDistance I Mstar := by sorry

end BipartiteVRM.Competitive
