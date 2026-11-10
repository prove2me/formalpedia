-- Prove2me | Theorems.Thm_BhangaleHypergraph_Main_outer_completeness
-- name    : BhangaleHypergraph.Main.outer_completeness
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-09T14:05:55.799954+00:00
-- url     : https://prove2.me/theorems/7b0a4a34-d61d-466a-bf1f-77204c40fd9a
-- title:
--   Lemma 2.6 — Outer completeness
-- statement:
--   For every biregular base Label Cover instance $L$ and $\ell\ge2$, if one base labeling satisfies every occurrence, then all radius-$2(\ell-i)$ neighborhoods admit a simultaneous choice of locally satisfying labels, and every restriction constraint between every layer pair is satisfied:
--   $$\operatorname{SAT}(L)\Longrightarrow\operatorname{SAT}(\operatorname{Neighborhood}(L,\ell)).$$
--   The choice is simultaneous across all layers and centers; it is not a separate witness for each constraint.
--
--   This gives the perfect-completeness clause for the concrete neighborhood outer construction.
--
--   Differences from the source:
--   - encoding: one-based finite label and color sets → zero-based Fin types and finite subsets; reason: subtracting one gives a bijection and preserves every instance
--   - encoding: enumerated local assignment labels and restriction projections → local assignments with canonical zeros outside their balls and equality on the target ball; reason: indexing the finite assignment sets by any bijection yields exactly the source labelings and constraints
-- source:
--   Amey Bhangale, STOC 2027 submission #1052 (October 2026), Lemma 2.6, p. 8 (PDF p. 8); https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/1052.pdf

import Definitions.Def_BhangaleHypergraph_Main_Base

namespace BhangaleHypergraph.Main

theorem outer_completeness (B : BaseCover) (ell : ℕ) (hell : 2 ≤ ell)
    (hsat : BaseSatisfiable B) :
    ∃ σ : NeighborhoodLabeling B ell,
      ∀ (i j : Fin ell), i < j → ∀ e e' : Fin B.E, B.right e = B.right e' →
        RestrictionSatisfied B σ i j e e' := by sorry

end BhangaleHypergraph.Main
