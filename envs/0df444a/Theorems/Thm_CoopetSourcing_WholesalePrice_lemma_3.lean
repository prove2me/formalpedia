-- Prove2me | Theorems.Thm_CoopetSourcing_WholesalePrice_lemma_3
-- name    : CoopetSourcing.WholesalePrice.lemma_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-19T06:52:12.240984+00:00
-- url     : https://prove2.me/theorems/6c7cf7ae-5039-4cef-881b-674d81b8c3f5
-- title:
--   Lemma 3, p. 18 — the VI is better off supplying the DO if wA > 126(17 − 3√34)/(570√34 − 15829)
-- statement:
--   Let $t$ be the size of the demand shock and $w_A$ the outside price, with $\underline t \le t$ and
--   $$\frac{126(17 - 3\sqrt{34})}{570\sqrt{34} - 15829} < w_A < \frac12 - \frac{5t}{7},$$
--   where $\underline t = 28(4 + 5\sqrt2)/1105 \approx 0.2805$ and the left bound is $\approx 0.005$. Then the VI is better off supplying the DO: there is a wholesale price $w_I$ with $0 \le w_I < \bar w_I$ such that
--   $$\Pi_I(w_I) > \Pi^{n*}_I,$$
--   where $\Pi_I$ is the VI's expected profit (6), $\bar w_I$ the pooling cap (4) above which the DO buys nothing from her, and $\Pi^{n*}_I = (3 + 4w_A)^2/100$ her profit without a partnership.
--
--   The supply partnership with a rival is thus profitable for the VI throughout the parameter region of the paper's analysis.
--
--   **Formalization Note** The conclusion reads the proof's $\max_{w_I \in [0, \bar w_I]}\Pi_I(w_I) > \Pi^{n*}_I$. The hypothesis $t \ge \underline t$ is added: the paper states it on p. 18 just after Lemma 3, and for very small $t$ ($t < 0.029$) the thresholds satisfy $\bar w_{sep/pool} > \bar w_I$, (6) is ill-posed and the lemma fails. $\bar w_I$ is the corrected (4), with the radical over $34$ only; with the typeset form the lemma is false in a large part of the region.
-- source:
--   Jung & Kouvelis, “On Co-opetitive Supply Partnerships with End-Product Rivals”, SSRN preprint 3555184 (PDF of 2020-03-06), p. 18, Lemma 3; proof on Online Supplement p. S5

import Mathlib
import Definitions.Def_CoopetSourcing_WholesalePrice_Model

namespace CoopetSourcing.WholesalePrice

theorem lemma_3 (t wA : ℝ) (h : Standing t wA) : ∃ wI : ℝ, 0 ≤ wI ∧ wI < wIBar t wA ∧ profitNo t wA < profitVI t wA wI := by sorry

end CoopetSourcing.WholesalePrice
