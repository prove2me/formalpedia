-- Prove2me | Theorems.Thm_CoopetSourcing_WholesalePrice_lemma_5_gap_limit_sign
-- name    : CoopetSourcing.WholesalePrice.lemma_5_gap_limit_sign
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-19T06:52:05.479221+00:00
-- url     : https://prove2.me/theorems/3314e33c-669f-4de1-bfa3-5c1733cf5d9f
-- title:
--   Proof of Lemma 5, p. S6 — the limit (153(√5134 − 122)t + 125√(21t(51t + 52)))/5250 is positive iff t < t̄
-- statement:
--   Let $\bar t$ be a nonzero real solution of equation (7),
--   $$153(\sqrt{5134} - 122)\,\bar t + 125\sqrt{21\bar t(51\bar t + 52)} = 0$$
--   ($\bar t \approx 0.4005$). For $35/92 < t < 7/10$, let $L$ be the left limit of $\bar w_{sep/pool} - \bar{\bar w}_{equal}$ as $w_A$ approaches $1/2 - 5t/7$. Then
--   $$L > 0 \iff t < \bar t.$$
--
--   The companion milestone identifies $L$ with $(153(\sqrt{5134}-122)t + 125\sqrt{21t(51t+52)})/5250$. Thus a separating outcome is possible near the top of the parameter region exactly when demand uncertainty is below $\bar t$.
--
--   **Formalization Note** The Lean asserts existence of the one-sided limit and its sign equivalence. The range $35/92<t<7/10$ keeps the comparison in the region analyzed in the paper.
-- source:
--   Jung & Kouvelis, “On Co-opetitive Supply Partnerships with End-Product Rivals”, SSRN preprint 3555184 (PDF of 2020-03-06), Online Supplement p. S6, proof of Lemma 5; eq. (7), p. 18

import Mathlib
import Definitions.Def_CoopetSourcing_WholesalePrice_Model

namespace CoopetSourcing.WholesalePrice

theorem lemma_5_gap_limit_sign (tbar : ℝ) (htbar : tbar ≠ 0) (h7 : Eq7 tbar)
    (t : ℝ) (ht : 35 / 92 < t) (ht7 : t < 7 / 10) :
    ∃ L : ℝ,
      Filter.Tendsto (fun wA : ℝ => wSepPool t wA - wEqualBar t wA)
        (nhdsWithin (1 / 2 - 5 * t / 7) (Set.Iio (1 / 2 - 5 * t / 7))) (nhds L) ∧
      (0 < L ↔ t < tbar) := by sorry

end CoopetSourcing.WholesalePrice
