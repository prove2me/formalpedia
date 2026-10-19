-- Prove2me | Theorems.Thm_CoopetSourcing_WholesalePrice_eq_13
-- name    : CoopetSourcing.WholesalePrice.eq_13
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-19T06:52:04.445963+00:00
-- url     : https://prove2.me/theorems/de2b1d85-3a55-40e5-8de4-7074d94a139b
-- title:
--   (13), proof of Lemma 5, p. S6 — the pooling profit Πp_I is uniquely maximized over ℝ at (3703 − 4066t − 242wA)/9204
-- statement:
--   Let $\Pi^p_I(w_I)$ be the VI's expected profit in the pooling equilibrium of Lemma 2, as a function of her wholesale price $w_I$, for demand-shock size $t$ and outside price $w_A$. For all real $t$, $w_A$, the point
--   $$w^\circ = \frac{3703 - 4066t - 242w_A}{9204}$$
--   is the unique maximizer of $\Pi^p_I$ over $w_I \in \mathbb R$: for every $w_I \ne w^\circ$,
--   $$\Pi^p_I(w_I) < \Pi^p_I(w^\circ).$$
--
--   This is equation (13) of the proof of Lemma 5. It locates the unconstrained pooling optimum, which the proofs of Lemma 5 and Proposition 4 compare with the pooling cap $\bar w_I$.
-- source:
--   Jung & Kouvelis, “On Co-opetitive Supply Partnerships with End-Product Rivals”, SSRN preprint 3555184 (PDF of 2020-03-06), Online Supplement p. S6, proof of Lemma 5, eq. (13)

import Mathlib
import Definitions.Def_CoopetSourcing_WholesalePrice_Model

namespace CoopetSourcing.WholesalePrice

theorem eq_13 (t wA wI : ℝ) (hwI : wI ≠ (3703 - 4066 * t - 242 * wA) / 9204) : profitPool t wA wI < profitPool t wA ((3703 - 4066 * t - 242 * wA) / 9204) := by sorry

end CoopetSourcing.WholesalePrice
