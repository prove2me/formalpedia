-- Prove2me | Theorems.Thm_FengLiYangMatching_General_Supplement_theorem_1_3
-- name    : FengLiYangMatching.General.Supplement.theorem_1_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T03:24:15.292821+00:00
-- url     : https://prove2.me/theorems/c36beb28-368e-442c-a8cc-93d97c62e25c
-- title:
--   Theorem 1.3 — General upper bound: 0.6964
-- statement:
--   There exist a finite simple graph $G$ on $[n]$ and $\mathrm{OPT}(G)>0$ such that every randomized online policy $P$, even when selected with knowledge of $G$, has some labelling $\pi$ for which
--
--   $$\mathbb E_{t,\xi}[\mathrm{ALG}_P(\pi(G),t,\xi)]\le\frac{1741}{2500}\,\mathrm{OPT}(G).$$
--
--   Each edge has an independent uniform arrival time in $[0,1]$, and the policy observes both the arriving edge and its time. Private randomness is independent of arrivals. The policy is quantified after $G$ and before $\pi$: it knows the graph up to isomorphism, but not the chosen labels or future edges. Therefore no such algorithm has competitive ratio greater than 0.6964. This companion theorem bounds the general-graph problem.
--
--   Differences from the source:
--   - encoding: arbitrary finite labelled vertex set → Fin n and unordered Sym2 edges, for every natural n; reason: every finite simple graph has such a labelling; the representation removes no instance
--   - encoding: expected matching size for randomized online algorithms → lower Lebesgue integrals of ENNReal-valued finite counts with one independent uniform real seed; reason: one seed encodes private randomness; measurable policies retain their ordinary expectations and no Bochner default is used
--   - encoding: known up to isomorphism; no competitive ratio greater than 0.6964 → there exists a positive-optimum graph, then for every timed policy there exists a bad vertex permutation with expected size at most (1741/2500) OPT; reason: this quantifier order supplies the graph to the algorithm before hiding its labels, exactly as in Section 5
-- source:
--   Yilong Feng, Haolong Li, Zonghan Yang, Improved Bounds for Online Matching with Random Edge Arrivals, STOC 2027 submission #1018 (October 2026), Theorem 1.3, p. 3 (setup/proof: §5, pp. 17–19).

import Definitions.Def_FengLiYangMatching_General_Supplement_OnlineModel

open MeasureTheory Finset
open scoped BigOperators ENNReal

set_option autoImplicit false

namespace FengLiYangMatching.General.Supplement

theorem theorem_1_3 :
    ∃ n : ℕ, ∃ G : SimpleGraph (Fin n), 0 < OPT G ∧
      ∀ P : TimedPolicy n, ∃ labelling : Equiv.Perm (Fin n),
        timedValue (relabel G labelling) P ≤ ENNReal.ofReal ((1741/2500 : ℝ) * (OPT G : ℝ)) := by sorry

end FengLiYangMatching.General.Supplement
