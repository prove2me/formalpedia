-- Prove2me | Theorems.Thm_ComplementsRev_Approx_proposition_5_10
-- name    : ComplementsRev.Approx.proposition_5_10
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-18T22:15:56.541039+00:00
-- url     : https://prove2.me/theorems/50cf2efb-3176-4fe7-8ad8-d7371b83a16b
-- title:
--   Proposition 5.10 — NON-FAVORITE bound
-- statement:
--   For the finite product hyperedge population $D$ and any fixed tie rank for favorite hyperedge regions,
--
--   $$\operatorname{NON\text{-}FAVORITE}(D)\le12\,\operatorname{BREV}(D).$$
--
--   This is the nonfavorite contribution needed for the paper's main approximation guarantee.
--
--   **Formalization Note** No exact cutoff is assumed. The paper's proof selects a cutoff with a prescribed tail mass, which need not exist for a finite-support population.
-- source:
--   Eden, Feldman, Friedler, Talgam-Cohen & Weinberg, A Simple and Approximately Optimal Mechanism for a Buyer with Complements, arXiv:1612.04746v2, Proposition 5.10, p. 13

import Mathlib
import Definitions.Def_ComplementsRev_Approx_Setting

namespace ComplementsRev.Approx

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Eden et al., Proposition 5.10, p. 13: the NON-FAVORITE bound. -/
theorem proposition_5_10 (P : Population ι) (rk : Finset ι → ℕ)
    (hrk : Function.Injective rk) :
    NONFAV P rk ≤ 12 * BREV P := by sorry

end ComplementsRev.Approx
