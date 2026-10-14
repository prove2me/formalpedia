-- Prove2me | Theorems.Thm_DROReview_PhiDiv_hellinger_le_kl
-- name    : DROReview.PhiDiv.hellinger_le_kl
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-13T21:17:01.106514+00:00
-- url     : https://prove2.me/theorems/c536804c-da6f-4fb6-a67b-83099039e619
-- title:
--   Footnote 18 and Lemma 5.4 — Hellinger divergence is at most KL
-- statement:
--   For any probability measures $P$ and $P_0$ on the same measurable space, the Hellinger divergence does not exceed the Kullback–Leibler divergence:
--
--   $$
--   \mathfrak D^{\phi_h}(P,P_0)\le\mathfrak D^{\phi_{\mathrm{kl}}}(P,P_0).
--   $$
--
--   This is the second comparison in (5.10) and is repeated explicitly in footnote 18. It implies that every KL ambiguity ball lies in the Hellinger ball of the same radius.
--
--   **Formalization Note** Both divergences take values in $[0,+\infty]$. No absolute-continuity assumption is imposed; the extended divergence handles singular pairs.
-- source:
--   Rahimian, Mehrotra, Distributionally Robust Optimization: A Review, arXiv:1908.05659v1 (2019), p. 34, Lemma 5.4, (5.10), second inequality; p. 35, footnote 18

import Definitions.Def_DROReview_PhiDiv_phiDiv
import Definitions.Def_DROReview_PhiDiv_generators

namespace DROReview.PhiDiv

open MeasureTheory

/-- Footnote 18, p. 35, and Lemma 5.4, (5.10), second inequality, p. 34. -/
theorem hellinger_le_kl {Ξ : Type*} [MeasurableSpace Ξ]
    (P P₀ : ProbabilityMeasure Ξ) :
    phiDiv phiH P P₀ ≤
      phiDiv phiKL P P₀ := by sorry

end DROReview.PhiDiv
