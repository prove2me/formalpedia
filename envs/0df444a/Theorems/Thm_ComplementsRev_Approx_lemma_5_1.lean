-- Prove2me | Theorems.Thm_ComplementsRev_Approx_lemma_5_1
-- name    : ComplementsRev.Approx.lemma_5_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-18T22:15:47.037989+00:00
-- url     : https://prove2.me/theorems/d98c111c-5de1-4bcc-a3dd-a1689fb272f3
-- title:
--   Lemma 5.1 — CORE and TAIL decomposition
-- statement:
--   Fix a real cutoff $t$ and a tie rank for the favorite hyperedge regions. CORE retains hyperedge weights at most $t$ inside the best feasible bundle; TAIL sums weights exceeding $t$ outside their favorite regions. Then
--
--   $$\operatorname{NON\text{-}FAVORITE}(D)\le \operatorname{CORE}(D,t)+\operatorname{TAIL}(D,t).$$
--
--   This separates the nonfavorite benchmark into a bounded-weight contribution and a large-weight contribution.
-- source:
--   Eden, Feldman, Friedler, Talgam-Cohen & Weinberg, A Simple and Approximately Optimal Mechanism for a Buyer with Complements, arXiv:1612.04746v2, Lemma 5.1, p. 10

import Mathlib
import Definitions.Def_ComplementsRev_Approx_Setting

namespace ComplementsRev.Approx

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Eden et al., Lemma 5.1, p. 10: split NON-FAVORITE at a cutoff. -/
theorem lemma_5_1 (P : Population ι) (rk : Finset ι → ℕ)
    (hrk : Function.Injective rk) (t : ℝ) :
    NONFAV P rk ≤ CORE P t + TAIL P rk t := by sorry

end ComplementsRev.Approx
