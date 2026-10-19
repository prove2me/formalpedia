-- Prove2me | Theorems.Thm_ComplementsRev_Approx_proposition_4_1
-- name    : ComplementsRev.Approx.proposition_4_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-18T22:15:55.522146+00:00
-- url     : https://prove2.me/theorems/cde1c33d-09c3-4416-a653-c6ec9b64438d
-- title:
--   Proposition 4.1 — SINGLE is bounded by simple revenues
-- statement:
--   Suppose the population $D$ has complementarity degree at most $d$. For every fixed tie rank defining favorite hyperedge regions,
--
--   $$\operatorname{SINGLE}(D)\le 4d\,\operatorname{SREV}^{*}(D)+4\,\operatorname{BREV}(D).$$
--
--   This bounds the favorite-hyperedge term in the duality benchmark by the two simple mechanisms.
--
--   **Formalization Note** SREV* uses the paper's strict, conservative sold-item indicator, and the complementarity condition counts hyperedges whose weight can be positive.
-- source:
--   Eden, Feldman, Friedler, Talgam-Cohen & Weinberg, A Simple and Approximately Optimal Mechanism for a Buyer with Complements, arXiv:1612.04746v2, Proposition 4.1, p. 7; proof p. 10

import Mathlib
import Definitions.Def_ComplementsRev_Approx_Setting

namespace ComplementsRev.Approx

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Eden et al., Proposition 4.1, p. 7: the SINGLE bound. -/
theorem proposition_4_1 (P : Population ι) (d : ℕ) (hd : HasComplementarity P d)
    (rk : Finset ι → ℕ) (hrk : Function.Injective rk) :
    SINGLE P rk ≤ 4 * (d : ℝ) * SREVstar P + 4 * BREV P := by sorry

end ComplementsRev.Approx
