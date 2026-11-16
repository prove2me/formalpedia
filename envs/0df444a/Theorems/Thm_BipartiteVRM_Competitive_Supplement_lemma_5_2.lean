-- Prove2me | Theorems.Thm_BipartiteVRM_Competitive_Supplement_lemma_5_2
-- name    : BipartiteVRM.Competitive.Supplement.lemma_5_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T19:29:33.949786+00:00
-- url     : https://prove2.me/theorems/7eb390f9-24cc-4059-a16f-5e3771d0771f
-- title:
--   Lemma 5.2 — weight change in $G_{uv}$ equals the γ-net-cost of $N\triangle M$
-- statement:
--   Let $M$ be a matching, let $u\ne v$ be vertices unsaturated by $M$, and let $G_{uv}$ be the complete graph on the vertices saturated by $M$ together with $u$ and $v$, weighted by $w_M(e)=D(e)$ for $e\in M$ and $w_M(e)=\gamma D(e)$ otherwise. Every perfect matching $N$ of $G_{uv}$ satisfies
--
--   $$w_M(N)-w_M(M)=\varphi_M(N\triangle M).$$
--
--   This identity converts the minimum-weight perfect matching computation of Step 1 into a statement about γ-net-costs of $N\triangle M$; it is used in Lemmas 5.3 and 5.5.
--
--   Differences from the source:
--   - generalization: M the offline matching at some state of non-bipartite VRM, u, v free requests, D the TA distance, fixed γ > 1 → any matching M on natural labels, any distinct M-unsaturated labels u, v, any edge function D : Edge → ℝ and any real γ; reason: the identity is an algebraic fact about finite edge sums and holds for every such M, D and γ; the source's state, requests, distance and γ are a special case
-- source:
--   Tung-Wei Kuo, STOC 2027 submission #528 (October 2026), p. 15, Lemma 5.2

import Definitions.Def_BipartiteVRM_Competitive_Supplement_Paths

set_option autoImplicit false

namespace BipartiteVRM.Competitive.Supplement

open MatchingDelays.Linear (Instance Edge)

/-- Lemma 5.2, p. 15. -/
theorem lemma_5_2 (D : Edge → ℝ) (γ : ℝ) (M : Matching) (hM : IsMatching M)
    (u v : ℕ) (huv : u ≠ v) (hu : ¬ saturated M u) (hv : ¬ saturated M v)
    (N : Matching) (hN : IsPerfectOn (pairVertices M u v) N) :
    weight D γ M N - weight D γ M M = netCost D γ M (symmD N M) := by sorry

end BipartiteVRM.Competitive.Supplement
