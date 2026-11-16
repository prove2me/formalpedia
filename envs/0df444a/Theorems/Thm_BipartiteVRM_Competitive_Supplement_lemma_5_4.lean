-- Prove2me | Theorems.Thm_BipartiteVRM_Competitive_Supplement_lemma_5_4
-- name    : BipartiteVRM.Competitive.Supplement.lemma_5_4
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T19:30:34.878195+00:00
-- url     : https://prove2.me/theorems/01480988-92ed-4a7e-bbf9-16eee35a066a
-- title:
--   Lemma 5.4 — edgewise switching costs before and after a symmetric difference
-- statement:
--   Let $M$ and $M'$ be matchings and $Q=M\triangle M'$. With $c_L(e)=-D(e)$ for $e\in L$ and $c_L(e)=\gamma D(e)$ otherwise:
--
--   1. every edge $e\notin Q$ satisfies $c_{M'}(e)=c_M(e)$;
--   2. every edge $e\in Q$ satisfies
--
--   $$c_M(e)+c_{M'}(e)=(\gamma-1)D(e).$$
--
--   These identities compare γ-net-costs with respect to the offline matchings before and after an augmentation, edge by edge, in the induction step of Lemma 5.5.
--
--   Differences from the source:
--   - generalization: matchings M, M′, D the TA distance, fixed γ > 1 → matchings M, M′ on natural labels, any edge function D : Edge → ℝ and any real γ; reason: both identities are case checks on membership and hold for every D and γ; the source's D and γ are a special case
-- source:
--   Tung-Wei Kuo, STOC 2027 submission #528 (October 2026), p. 16, Lemma 5.4 (a) and (b)

import Definitions.Def_BipartiteVRM_Competitive_Supplement_Paths

set_option autoImplicit false

namespace BipartiteVRM.Competitive.Supplement

open MatchingDelays.Linear (Instance Edge)

/-- Lemma 5.4, p. 16, both parts. -/
theorem lemma_5_4 (D : Edge → ℝ) (γ : ℝ) (M M' : Matching)
    (hM : IsMatching M) (hM' : IsMatching M') :
    (∀ e, e ∉ symmD M M' → switchCost D γ M' e = switchCost D γ M e) ∧
    (∀ e ∈ symmD M M', switchCost D γ M e + switchCost D γ M' e = (γ - 1) * D e) := by sorry

end BipartiteVRM.Competitive.Supplement
