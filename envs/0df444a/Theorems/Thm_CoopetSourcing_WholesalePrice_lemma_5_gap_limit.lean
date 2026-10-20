-- Prove2me | Theorems.Thm_CoopetSourcing_WholesalePrice_lemma_5_gap_limit
-- name    : CoopetSourcing.WholesalePrice.lemma_5_gap_limit
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-19T06:52:22.364619+00:00
-- url     : https://prove2.me/theorems/51312dd4-8e48-4d1e-8b9c-2994d7f9aaff
-- title:
--   Proof of Lemma 5, p. S6 — lim_{wA → 1/2 − 5t/7} (w̄sep/pool − w̿equal) = (153(√5134 − 122)t + 125√(21t(51t + 52)))/5250
-- statement:
--   Fix a demand-shock size $t$ with $35/92 < t < 7/10$. With $\bar w_{sep/pool}$ the separating/pooling threshold (3) and $\bar{\bar w}_{equal}$ the solution of $\Pi^{s,4}_I(w) = \Pi^p_I(\bar w_I)$ of (16), both as functions of the outside price $w_A$,
--   $$\lim_{w_A \uparrow 1/2 - 5t/7}\big(\bar w_{sep/pool} - \bar{\bar w}_{equal}\big) = \frac{153(\sqrt{5134} - 122)\,t + 125\sqrt{21t(51t + 52)}}{5250}.$$
--
--   Since the difference is increasing in $w_A$, this limit is its supremum over the parameter region, and its sign decides whether a separating outcome can occur at all.
--
--   **Formalization Note** The page prints $\bar t$ in the right-hand side where it means $t$ (the next sentence compares the sign of this expression with $t < \bar t$); the Lean writes $t$. The limit is taken from the left, inside the region $w_A < 1/2 - 5t/7$. The range $35/92 < t$ matches the use in the proofs; $t < 7/10$ makes $1/2 - 5t/7$ positive.
-- source:
--   Jung & Kouvelis, “On Co-opetitive Supply Partnerships with End-Product Rivals”, SSRN preprint 3555184 (PDF of 2020-03-06), Online Supplement p. S6, proof of Lemma 5

import Mathlib
import Definitions.Def_CoopetSourcing_WholesalePrice_Model

namespace CoopetSourcing.WholesalePrice

theorem lemma_5_gap_limit (t : ℝ) (ht : 35 / 92 < t) (ht7 : t < 7 / 10) : Filter.Tendsto (fun wA : ℝ => wSepPool t wA - wEqualBar t wA) (nhdsWithin (1 / 2 - 5 * t / 7) (Set.Iio (1 / 2 - 5 * t / 7))) (nhds ((153 * (Real.sqrt 5134 - 122) * t + 125 * Real.sqrt (21 * t * (51 * t + 52))) / 5250)) := by sorry

end CoopetSourcing.WholesalePrice
