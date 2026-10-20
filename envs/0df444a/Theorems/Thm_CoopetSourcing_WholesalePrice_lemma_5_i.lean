-- Prove2me | Theorems.Thm_CoopetSourcing_WholesalePrice_lemma_5_i
-- name    : CoopetSourcing.WholesalePrice.lemma_5_i
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-19T06:52:06.71888+00:00
-- url     : https://prove2.me/theorems/0c6ef081-ae6f-48b9-b3a3-acea62fc2120
-- title:
--   Lemma 5 (i), p. 18 — for t̲ ≤ t < t̄ there are thresholds w̲A, w̄A: separating optimum if wA > w̄A, pooling optimum if wA < w̲A
-- statement:
--   Let $\bar t \ne 0$ solve equation (7), $153(\sqrt{5134} - 122)\bar t + 125\sqrt{21\bar t(51\bar t + 52)} = 0$, and let $t$ satisfy $\underline t \le t < \bar t$, where $\underline t = 28(4 + 5\sqrt2)/1105$. Then there are thresholds $\underline w_A$ and $\bar w_A$, inside the parameter range ($\underline w < \underline w_A$ and $\bar w_A < 1/2 - 5t/7$, with $\underline w = 126(17 - 3\sqrt{34})/(570\sqrt{34} - 15829)$), such that for every outside price $w_A$ with $\underline w < w_A < 1/2 - 5t/7$:
--
--   1. if $w_A > \bar w_A$, the VI's equilibrium price lies in the separating range: some $w \in [0, \bar w_{sep/pool}]$ maximizes the expected profit (6) over all $w_I \ge 0$, i.e. $w_I^* = \arg\max_{w_I \in [0, \bar w_{sep/pool}]}\Pi^s_I(w_I)$;
--   2. if $w_A < \underline w_A$, the VI's equilibrium price is the pooling one: there is a maximizer $w$ of $\Pi^p_I$ over $[\bar w_{sep/pool}, \bar w_I]$ with
--   $$\Pi_I(w_I) \le \Pi^p_I(w) \quad\text{for all } w_I \ge 0,$$
--   and for every $\varepsilon>0$ a feasible $w_I\ge0$ satisfies $\Pi_I(w_I)>\Pi^p_I(w)-\varepsilon$,
--   i.e. $w_I^* = \arg\max_{w_I \in [\bar w_{sep/pool}, \bar w_I^{(-)}]}\Pi^p_I(w_I)$.
--
--   Lemma 5 is the qualitative dichotomy that Proposition 4 sharpens into a single threshold with explicit equilibrium prices.
--
--   **Formalization Note** "There exist $\underline w_A$ and $\bar w_A$" is read as thresholds strictly inside the parameter range; without $\underline w < \underline w_A$ and $\bar w_A < 1/2 - 5t/7$ any thresholds outside the range would make the statement vacuous. The pooling arg max over $[\bar w_{sep/pool}, \bar w_I^{(-)}]$ (whose right end is approached, not attained, since (6) drops at $\bar w_I$) is read as: the supremum of (6) over $w_I \ge 0$ equals the maximum of the continuous $\Pi^p_I$ on the closed interval, with feasible prices approaching that value. $\bar w_I$ is the corrected (4). Lemma 5 (ii) coincides word for word with Proposition 4 (ii) and is not stated separately.
-- source:
--   Jung & Kouvelis, “On Co-opetitive Supply Partnerships with End-Product Rivals”, SSRN preprint 3555184 (PDF of 2020-03-06), p. 18, Lemma 5 (i), eq. (7); proof on Online Supplement p. S6

import Mathlib
import Definitions.Def_CoopetSourcing_WholesalePrice_Model

namespace CoopetSourcing.WholesalePrice

theorem lemma_5_i (tbar : ℝ) (htbar : tbar ≠ 0) (h7 : Eq7 tbar) (t : ℝ) (ht : tLow ≤ t) (htb : t < tbar) :
    ∃ wAlo wAhi : ℝ, wALow < wAlo ∧ wAhi < 1 / 2 - 5 * t / 7 ∧ ∀ wA : ℝ, Standing t wA →
      (wAhi < wA → ∃ w ∈ Set.Icc 0 (wSepPool t wA),
          ∀ wI : ℝ, 0 ≤ wI → profitVI t wA wI ≤ profitVI t wA w) ∧
      (wA < wAlo → ∃ w ∈ Set.Icc (wSepPool t wA) (wIBar t wA),
          (∀ v ∈ Set.Icc (wSepPool t wA) (wIBar t wA), profitPool t wA v ≤ profitPool t wA w) ∧
          (∀ wI : ℝ, 0 ≤ wI → profitVI t wA wI ≤ profitPool t wA w) ∧
          ∀ ε : ℝ, 0 < ε → ∃ wI : ℝ, 0 ≤ wI ∧ profitPool t wA w - ε < profitVI t wA wI) := by sorry

end CoopetSourcing.WholesalePrice
