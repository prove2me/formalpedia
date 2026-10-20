-- Prove2me | Theorems.Thm_CoopetSourcing_WholesalePrice_lemma_5_gap_mono
-- name    : CoopetSourcing.WholesalePrice.lemma_5_gap_mono
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-19T06:52:16.648015+00:00
-- url     : https://prove2.me/theorems/3f3c88b4-1f28-4bc3-b124-7d5efcaf73bb
-- title:
--   Proofs of Lemma 5 and Prop. 4, pp. S6–S7 — for t > 35/92, w̄sep/pool − w̿equal is strictly increasing in wA
-- statement:
--   Fix a demand-shock size $t > 35/92 \approx 0.3804$. For an outside price $w_A$, let $\bar w_{sep/pool}(w_A)$ be the separating/pooling threshold (3) and $\bar{\bar w}_{equal}(w_A)$ the price at which the VI's separating profit on its last piece, $\Pi^{s,4}_I$, equals the pooling profit at the cap, $\Pi^p_I(\bar w_I)$ (equation (16)). Then
--   $$w_A \longmapsto \bar w_{sep/pool}(w_A) - \bar{\bar w}_{equal}(w_A)$$
--   is strictly increasing on the interval $126(17 - 3\sqrt{34})/(570\sqrt{34} - 15829) < w_A < 1/2 - 5t/7$.
--
--   This monotonicity is what makes the separating region an upper interval in $w_A$, so that a single threshold $\bar w_A$ separates the two outcomes in Proposition 4.
--
--   **Formalization Note** The page states $\partial(\bar w_{sep/pool} - \bar{\bar w}_{equal})/\partial w_A > 0$ for $t \ge 0.4004$ (p. S6) and uses it for $t > 35/92$ (p. S7); the hypothesis is the union, $t > 35/92$. The derivative claim is stated as strict monotonicity, which needs no differentiability side condition. $\bar{\bar w}_{equal}$ is the root on the increasing branch $w \le (1 + t)/2$ of the quadratic $\Pi^{s,4}_I$, and $\bar w_I$ is the corrected (4).
-- source:
--   Jung & Kouvelis, “On Co-opetitive Supply Partnerships with End-Product Rivals”, SSRN preprint 3555184 (PDF of 2020-03-06), Online Supplement p. S6, proof of Lemma 5 (eq. (16) and the sentence after it); p. S7, proof of Proposition 4

import Mathlib
import Definitions.Def_CoopetSourcing_WholesalePrice_Model

namespace CoopetSourcing.WholesalePrice

theorem lemma_5_gap_mono (t : ℝ) (ht : 35 / 92 < t) : StrictMonoOn (fun wA : ℝ => wSepPool t wA - wEqualBar t wA) (Set.Ioo wALow (1 / 2 - 5 * t / 7)) := by sorry

end CoopetSourcing.WholesalePrice
