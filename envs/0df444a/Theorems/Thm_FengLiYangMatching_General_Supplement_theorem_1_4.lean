-- Prove2me | Theorems.Thm_FengLiYangMatching_General_Supplement_theorem_1_4
-- name    : FengLiYangMatching.General.Supplement.theorem_1_4
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T03:24:50.800678+00:00
-- url     : https://prove2.me/theorems/9b1a87ce-ff06-4e23-a06f-65361ee7c609
-- title:
--   Theorem 1.4 — Bipartite upper bound: 0.7043
-- statement:
--   There exist a finite bipartite simple graph $G$ on $[n]$ and $\mathrm{OPT}(G)>0$ such that for every randomized online policy $P$ selected after $G$ is known, some vertex labelling $\pi$ satisfies
--
--   $$\mathbb E_{t,\xi}[\mathrm{ALG}_P(\pi(G),t,\xi)]\le\frac{7043}{10000}\,\mathrm{OPT}(G).$$
--
--   Policies observe real arrival times as well as edges and have independent private randomness. The selected labelling is hidden and future edges are unavailable. Bipartiteness is expressed by existence of a proper two-colouring, with no extra condition on the algorithm. Hence no online algorithm has competitive ratio greater than 0.7043 on bipartite graphs, even when the input graph is known up to isomorphism. This is the bipartite companion upper bound.
--
--   Differences from the source:
--   - encoding: arbitrary finite labelled vertex set → Fin n and unordered Sym2 edges, for every natural n; reason: every finite simple graph has such a labelling; the representation removes no instance
--   - encoding: expected matching size for randomized online algorithms → lower Lebesgue integrals of ENNReal-valued finite counts with one independent uniform real seed; reason: one seed encodes private randomness; measurable policies retain their ordinary expectations and no Bochner default is used
--   - encoding: bipartite graph known up to isomorphism; no competitive ratio greater than 0.7043 → there exists a graph with Colorable 2 and positive optimum, then for every timed policy there exists a bad vertex permutation at the exact 7043/10000 bound; reason: two-colourability is bipartiteness and the quantifier order hides only the chosen labelling, as in Section 5
-- source:
--   Yilong Feng, Haolong Li, Zonghan Yang, Improved Bounds for Online Matching with Random Edge Arrivals, STOC 2027 submission #1018 (October 2026), Theorem 1.4, p. 3 (setup/proof: §5, pp. 17–19).

import Definitions.Def_FengLiYangMatching_General_Supplement_OnlineModel

open MeasureTheory Finset
open scoped BigOperators ENNReal

set_option autoImplicit false

namespace FengLiYangMatching.General.Supplement

theorem theorem_1_4 :
    ∃ n : ℕ, ∃ G : SimpleGraph (Fin n), G.Colorable 2 ∧ 0 < OPT G ∧
      ∀ P : TimedPolicy n, ∃ labelling : Equiv.Perm (Fin n),
        timedValue (relabel G labelling) P ≤ ENNReal.ofReal ((7043/10000 : ℝ) * (OPT G : ℝ)) := by sorry

end FengLiYangMatching.General.Supplement
