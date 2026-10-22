-- Prove2me | Theorems.Thm_DROReview_PhiDiv_kl_le_j
-- name    : DROReview.PhiDiv.kl_le_j
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-13T21:17:01.744544+00:00
-- url     : https://prove2.me/theorems/2912d7a5-bd26-403c-a650-ced0b24d21e4
-- title:
--   Lemma 5.4, (5.10) — KL divergence is at most J-divergence
-- statement:
--   For any probability measures $P$ and $P_0$ on the same measurable space, the Kullback–Leibler divergence is bounded by the J-divergence:
--
--   $$
--   \mathfrak D^{\phi_{\mathrm{kl}}}(P,P_0)\le\mathfrak D^{\phi_j}(P,P_0).
--   $$
--
--   This is the third comparison in (5.10). It gives the same-radius inclusion of the J-divergence ambiguity ball in the KL ball, including when either divergence is infinite.
--
--   **Formalization Note** The J generator is $+\infty$ at zero, as required for this inequality to hold when $P$ vanishes on a set charged by $P_0$.
-- source:
--   Rahimian, Mehrotra, Distributionally Robust Optimization: A Review, arXiv:1908.05659v1 (2019), p. 34, Lemma 5.4, (5.10), third inequality

import Definitions.Def_DROReview_PhiDiv_phiDiv
import Definitions.Def_DROReview_PhiDiv_generators

namespace DROReview.PhiDiv

open MeasureTheory

/-- Lemma 5.4, (5.10), third inequality, p. 34. -/
theorem kl_le_j {Ξ : Type*} [MeasurableSpace Ξ]
    (P P₀ : ProbabilityMeasure Ξ) :
    phiDiv phiKL P P₀ ≤
      phiDiv phiJ P P₀ := by sorry

end DROReview.PhiDiv
