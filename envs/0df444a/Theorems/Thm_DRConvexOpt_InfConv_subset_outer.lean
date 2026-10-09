-- Prove2me | Theorems.Thm_DRConvexOpt_InfConv_subset_outer
-- name    : DRConvexOpt.InfConv.subset_outer
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-09T03:38:36.677163+00:00
-- url     : https://prove2.me/theorems/6abae899-fc4d-40ed-839d-0df60f2ec123
-- title:
--   p. 12 — the ambiguity set 𝒫 is contained in every outer approximation 𝒫^j
-- statement:
--   Let $\mathcal P$ be the standardized ambiguity set (4) and let $\{\mathcal I_j\}_{j\in\mathcal J}$ be a partition of the index set of its confidence sets, given by a block map. Then for every block $j$,
--   $$\mathcal P \subseteq \mathcal P^j,$$
--   where $\mathcal P^j$ imposes only the probability conditions $\mathbb P[(\tilde z,\tilde u) \in \mathcal C_i] \in [\underline p_i,\overline p_i]$ for $i \in \mathcal I_j$, together with the expectation condition of $\mathcal P$.
--
--   This inclusion is what makes the naïve approximation (6) conservative, and it is the first inequality in the proof of Theorem 3.
--
--   **Formalization Note** The statement holds for every block map (surjective or not), without any of the standing conditions (C1)–(C3).
-- source:
--   Wiesemann, Kuhn & Sim, Distributionally Robust Convex Optimization, Optimization Online preprint 3757 (version of September 22, 2013), p. 12, sentence following the definition of 𝒫^j

import Mathlib
import Definitions.Def_DRConvexOpt_InfConv_Setting

namespace DRConvexOpt.InfConv

open MeasureTheory Matrix Filter Topology

/-- p. 12: the ambiguity set 𝒫 is a subset of each outer approximation 𝒫^j. -/
theorem subset_outer {nP nQ nK nI nJ : ℕ} (d : AmbData nP nQ nK nI)
    (blk : Fin (nI + 1) → Fin nJ) (j : Fin nJ) :
    ambiguitySet d ⊆ outerSet d blk j := by sorry

end DRConvexOpt.InfConv
