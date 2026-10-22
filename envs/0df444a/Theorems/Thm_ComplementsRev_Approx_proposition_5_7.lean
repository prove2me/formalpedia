-- Prove2me | Theorems.Thm_ComplementsRev_Approx_proposition_5_7
-- name    : ComplementsRev.Approx.proposition_5_7
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-18T22:15:53.841683+00:00
-- url     : https://prove2.me/theorems/4ae9be8f-9838-4e81-a608-99431e3793fd
-- title:
--   Proposition 5.7 — TAIL bound
-- statement:
--   For any real cutoff $t$ and any fixed tie rank for favorite hyperedge regions,
--
--   $$\operatorname{TAIL}(D,t)\le\left(\sum_{T\subseteq M}\Pr[w(T)>t]\right)\operatorname{BREV}(D).$$
--
--   This controls the large-weight part of NON-FAVORITE by grand-bundle revenue and the expected count of hyperedges above the cutoff.
--
--   **Formalization Note** TAIL keeps the region indicator even when hyperedges tie, because replacing it by a strict larger-weight event would change the quantity.
-- source:
--   Eden, Feldman, Friedler, Talgam-Cohen & Weinberg, A Simple and Approximately Optimal Mechanism for a Buyer with Complements, arXiv:1612.04746v2, Proposition 5.7, p. 13

import Mathlib
import Definitions.Def_ComplementsRev_Approx_Setting

namespace ComplementsRev.Approx

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Eden et al., Proposition 5.7, p. 13: the TAIL estimate. -/
theorem proposition_5_7 (P : Population ι) (rk : Finset ι → ℕ)
    (hrk : Function.Injective rk) (t : ℝ) :
    TAIL P rk t ≤
      (∑ T : Finset ι, P.Pr (fun w => t < w T)) * BREV P := by sorry

end ComplementsRev.Approx
