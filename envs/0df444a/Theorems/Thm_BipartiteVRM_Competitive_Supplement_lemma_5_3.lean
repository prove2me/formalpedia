-- Prove2me | Theorems.Thm_BipartiteVRM_Competitive_Supplement_lemma_5_3
-- name    : BipartiteVRM.Competitive.Supplement.lemma_5_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T19:30:09.204456+00:00
-- url     : https://prove2.me/theorems/cdd9f2ae-3efe-4e9d-a586-44d9ca20533a
-- title:
--   Lemma 5.3 — without negative alternating even cycles, $M\triangle Q_{uv}$ is a minimum-weight perfect matching
-- statement:
--   Let $M$ be a matching such that every simple $M$-alternating even cycle $C$ has $\varphi_M(C)\ge0$. Let $u\ne v$ be $M$-unsaturated, let $N_{uv}$ be any minimum-weight perfect matching of $G_{uv}$ under $w_M$, and let $Q_{uv}$ be the component of $N_{uv}\triangle M$ containing $u$ (the $M$-augmenting path from $u$ to $v$ in $N_{uv}\triangle M$). Then
--
--   $$M\triangle Q_{uv}\ \text{is a minimum-weight perfect matching of } G_{uv}.$$
--
--   Together with Lemma 5.2, this shows that Steps 1–2 return true minimum augmenting paths whenever the cycle condition holds, which Lemma 5.5 supplies at every state.
--
--   Differences from the source:
--   - generalization: M the offline matching at some state of non-bipartite VRM, u, v free requests, D the TA distance, fixed γ > 1 → any matching M on natural labels, any distinct M-unsaturated labels u, v, any edge function D : Edge → ℝ and any real γ; reason: the proof uses only additivity of φ_M and the structure of N △ M, valid for every such M, D and γ; the source's state, requests, distance and γ are a special case
--   - encoding: Q_uv, the M-augmenting path from u to v in N_uv △ M, for the N_uv computed in Step 1 → the connected component of N △ M containing u, for every minimum-weight perfect matching N of G_uv; reason: in N △ M the component of u is exactly that path (p. 15); quantifying over every minimum-weight N covers every Step 1 tie
-- source:
--   Tung-Wei Kuo, STOC 2027 submission #528 (October 2026), p. 15, Lemma 5.3 and Step 1 of §5.2

import Definitions.Def_BipartiteVRM_Competitive_Supplement_Paths

set_option autoImplicit false

namespace BipartiteVRM.Competitive.Supplement

open MatchingDelays.Linear (Instance Edge)

/-- Lemma 5.3, p. 15. Q_uv is the component of N_uv △ M containing u, for every
minimum-weight perfect matching N_uv of G_uv (every Step 1 tie). -/
theorem lemma_5_3 (D : Edge → ℝ) (γ : ℝ) (M : Matching) (hM : IsMatching M)
    (hcyc : ∀ C, AlternatingEvenCycle M C → 0 ≤ netCost D γ M (cycleEdges C)) :
    ∀ u v, u ≠ v → ¬ saturated M u → ¬ saturated M v →
      ∀ N, IsMinWeightPerfect D γ M u v N →
        IsMinWeightPerfect D γ M u v (symmD M (component (symmD N M) u)) := by sorry

end BipartiteVRM.Competitive.Supplement
