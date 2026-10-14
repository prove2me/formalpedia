-- Prove2me | Theorems.Thm_DROReview_PhiDiv_variation_sq_le_hellinger
-- name    : DROReview.PhiDiv.variation_sq_le_hellinger
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-13T21:17:01.464814+00:00
-- url     : https://prove2.me/theorems/c59e3a98-8973-4daf-b232-ce309e49831c
-- title:
--   Lemma 5.4, (5.10) — variation squared divided by four is at most Hellinger
-- statement:
--   Let $P$ and $P_0$ be probability measures on any measurable space. With the variation and Hellinger divergences of Table 1,
--
--   $$
--   \frac14\bigl(\mathfrak D^{\phi_v}(P,P_0)\bigr)^2
--     \le \mathfrak D^{\phi_h}(P,P_0).
--   $$
--
--   This is the first comparison in Lemma 5.4. It controls the paper's full $L^1$ variation divergence by Hellinger divergence, and gives the final radius conversion in (5.11).
--
--   **Formalization Note** The variation divergence is $\int|dP-dP_0|$, twice the total variation distance defined later in §5.1.3. The divergence includes singular mass and may be infinite.
-- source:
--   Rahimian, Mehrotra, Distributionally Robust Optimization: A Review, arXiv:1908.05659v1 (2019), p. 34, Lemma 5.4, (5.10), first inequality

import Definitions.Def_DROReview_PhiDiv_phiDiv
import Definitions.Def_DROReview_PhiDiv_generators

namespace DROReview.PhiDiv

open MeasureTheory

/-- Lemma 5.4, (5.10), first inequality, p. 34. The variation divergence
is the full L¹ distance, as in Table 1. -/
theorem variation_sq_le_hellinger {Ξ : Type*} [MeasurableSpace Ξ]
    (P P₀ : ProbabilityMeasure Ξ) :
    (1 / 4 : ENNReal) *
      (phiDiv phiV P P₀) ^ 2 ≤
      phiDiv phiH P P₀ := by sorry

end DROReview.PhiDiv
