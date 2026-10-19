-- Prove2me | Theorems.Thm_CoopetSourcing_WholesalePrice_lemma_3_limit
-- name    : CoopetSourcing.WholesalePrice.lemma_3_limit
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-19T06:52:07.612104+00:00
-- url     : https://prove2.me/theorems/b7e766b7-b3fb-4bbe-8f43-0d9af4bc3b7e
-- title:
--   Proof of Lemma 3, p. S5 — as wI ↑ w̄I, ΠI(wI) − Πn∗_I tends to (10t − 7 + 14wA)(60823 − 129730t − 221606wA + √34(22260t − 10290 + 7980wA))/2998800
-- statement:
--   Let $t$ be the size of the demand shock and $w_A$ the outside price, under the standing assumptions $\underline t \le t$, $\underline w < w_A < 1/2 - 5t/7$ (with $\underline t = 28(4 + 5\sqrt2)/1105$ and $\underline w = 126(17 - 3\sqrt{34})/(570\sqrt{34} - 15829)$). Let $\Pi_I$ be the VI's expected profit (6), $\bar w_I$ the pooling cap (4) and $\Pi^{n*}_I = (3 + 4w_A)^2/100$ her profit without a partnership. Then, as $w_I$ increases to $\bar w_I$ from below,
--   $$\lim_{w_I \uparrow \bar w_I}\Pi_I(w_I) = \Pi^{n*}_I + \frac{(10t - 7 + 14w_A)\big(60823 - 129730t - 221606w_A + \sqrt{34}\,(22260t - 10290 + 7980w_A)\big)}{2998800}.$$
--
--   The sign of this difference is what decides, in Lemma 3, whether selling to the rival beats walking away.
--
--   **Formalization Note** The page writes a two-sided limit; $\Pi_I$ jumps to $\Pi^{n*}_I$ at $\bar w_I$, so the limit is the left one, where $\Pi_I$ is the pooling profit (the page's "$\Pi^{S*}_I$" is a typo for $\Pi^{p*}_I$). The identity holds with the corrected (4), $\bar w_I = (245 - 350t - 70w_A - 6\sqrt{34}(7 - 10t - 14w_A))/420$; the page typesets the radical over $34(7 - 10t - 14w_A)$. The standing assumption $t \ge \underline t$ is stated on p. 18; it guarantees $\bar w_{sep/pool} < \bar w_I$, so that (6) is well posed.
-- source:
--   Jung & Kouvelis, “On Co-opetitive Supply Partnerships with End-Product Rivals”, SSRN preprint 3555184 (PDF of 2020-03-06), Online Supplement p. S5, proof of Lemma 3

import Mathlib
import Definitions.Def_CoopetSourcing_WholesalePrice_Model

namespace CoopetSourcing.WholesalePrice

theorem lemma_3_limit (t wA : ℝ) (h : Standing t wA) : Filter.Tendsto (profitVI t wA) (nhdsWithin (wIBar t wA) (Set.Iio (wIBar t wA))) (nhds (profitNo t wA + (10 * t - 7 + 14 * wA) * (60823 - 129730 * t - 221606 * wA + Real.sqrt 34 * (22260 * t - 10290 + 7980 * wA)) / 2998800)) := by sorry

end CoopetSourcing.WholesalePrice
