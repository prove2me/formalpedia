-- Prove2me | Theorems.Thm_CoopetSourcing_WholesalePrice_proposition_4
-- name    : CoopetSourcing.WholesalePrice.proposition_4
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-19T06:52:12.22798+00:00
-- url     : https://prove2.me/theorems/563a8266-6caa-4085-b8fc-ec62f7b18a64
-- title:
--   Proposition 4, p. 19 — the equilibrium wholesale price: w̄sep/pool iff t < t̄ and wA > w̄A, otherwise the pooling cap w̄I^(−)
-- statement:
--   Consider the VI's first-stage pricing problem: she chooses a wholesale price $w_I \ge 0$ to maximize her expected profit $\Pi_I(w_I)$ of equation (6), which equals the separating profit $\Pi^s_I(w_I)$ for $w_I \le \bar w_{sep/pool}$, the pooling profit $\Pi^p_I(w_I)$ for $\bar w_{sep/pool} < w_I < \bar w_I$, and the no-partnership profit $\Pi^{n*}_I$ for $w_I \ge \bar w_I$. Assume $\underline t \le t$ and $\underline w < w_A < 1/2 - 5t/7$, with $\underline t = 28(4 + 5\sqrt2)/1105 \approx 0.2805$ and $\underline w = 126(17 - 3\sqrt{34})/(570\sqrt{34} - 15829) \approx 0.005$. Let $\bar t \ne 0$ be a solution of (7),
--   $$153(\sqrt{5134} - 122)\,\bar t + 125\sqrt{21\bar t(51\bar t + 52)} = 0 \qquad (\bar t \approx 0.4005).$$
--
--   1. **Low demand uncertainty**, $\underline t \le t < \bar t$. There is $\bar w_A > 0$ with $\Pi^s_I(\bar w_{sep/pool}) = \Pi^p_I(\bar w_I)$ (both evaluated at $w_A = \bar w_A$) such that for every admissible $w_A$:
--      - if $w_A > \bar w_A$, then $w_I^* = \bar w_{sep/pool}$: this price is nonnegative and is the unique maximizer of $\Pi_I$ over $w_I \ge 0$;
--      - if $w_A \le \bar w_A$, then $w_I^* = \bar w_I^{(-)}$: $\Pi_I(w_I) \le \Pi^p_I(\bar w_I)$ for all $w_I \ge 0$, and $\Pi_I(w_I) \to \Pi^p_I(\bar w_I)$ as $w_I \uparrow \bar w_I$.
--   2. **High demand uncertainty**, $t \ge \bar t$. For every admissible $w_A$, $w_I^* = \bar w_I^{(-)}$ in the sense just described.
--
--   The VI buys the DO's demand information with a price concession (the separating price $\bar w_{sep/pool}$) only when demand uncertainty is low and the outside supply market is inefficient; otherwise she prices just below the level at which the DO would leave the partnership, and the DO pools and dual sources in high demand.
--
--   **Formalization Note** $\bar w_I$ is the corrected (4), $(245 - 350t - 70w_A - 6\sqrt{34}(7 - 10t - 14w_A))/420$; the page typesets the radical over $34(7 - 10t - 14w_A)$, which makes the proposition false in part of the region. "$w_I^* = \bar w_I^{(-)}$" is stated as an upper bound together with the left limit: $\Pi_I$ drops to $\Pi^{n*}_I$ at $\bar w_I$. At the crossing $w_A=\bar w_A$, the separating boundary may attain the same supremum. The quantity-subgame equilibria (Lemmas 1–2, Proposition 3) enter only through the closed forms in (6). The standing assumptions are the paper's (pp. 10 and 18).
-- source:
--   Jung & Kouvelis, “On Co-opetitive Supply Partnerships with End-Product Rivals”, SSRN preprint 3555184 (PDF of 2020-03-06), p. 19, Proposition 4; proof on Online Supplement p. S7

import Mathlib
import Definitions.Def_CoopetSourcing_WholesalePrice_Model

namespace CoopetSourcing.WholesalePrice

theorem proposition_4 (tbar : ℝ) (htbar : tbar ≠ 0) (h7 : Eq7 tbar) :
    (∀ t : ℝ, tLow ≤ t → t < tbar →
      ∃ wAbar : ℝ, 0 < wAbar ∧
        profitSep t wAbar (wSepPool t wAbar) = profitPool t wAbar (wIBar t wAbar) ∧
        ∀ wA : ℝ, Standing t wA →
          (wAbar < wA → MaxAtSepPool t wA) ∧ (wA ≤ wAbar → SupAtPoolCap t wA)) ∧
    (∀ t wA : ℝ, tbar ≤ t → Standing t wA → SupAtPoolCap t wA) := by sorry

end CoopetSourcing.WholesalePrice
