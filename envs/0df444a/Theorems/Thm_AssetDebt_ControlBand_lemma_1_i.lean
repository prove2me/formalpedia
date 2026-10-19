-- Prove2me | Theorems.Thm_AssetDebt_ControlBand_lemma_1_i
-- name    : AssetDebt.ControlBand.lemma_1_i
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-19T01:13:57.726756+00:00
-- url     : https://prove2.me/theorems/aa38e12f-09bc-4eb9-9c99-41933d1dfee4
-- title:
--   Lemma 1(i), p. 8 — working capital covering the discounted remaining debt makes the equity value $U_t + w_t - \sum_{i=t}^m \rho^{i-t} d_i$
-- statement:
--   Consider a debt schedule $d = (d_i)$ with $d_i \ge 0$ and maturity $m$, $1 \le m \le T$, and a period $1 \le t \le m$. Let the inventory be $x \in [0,1]$, the working capital $w \ge 0$ and the price $p > 0$. If the working capital covers the discounted remaining debt,
--
--   $$w \ \ge\ \sum_{i=t}^{m} \rho^{\,i-t} d_i ,$$
--
--   then the equity value equals the debt-free value plus the surplus working capital:
--
--   $$V_t(x, w, p; d) \;=\; U_t(x, p) + w - \sum_{i=t}^{m} \rho^{\,i-t} d_i .$$
--
--   In words, once the remaining debt is secured, bankruptcy cannot occur and the seller follows the revenue-maximizing policy of the debt-free problem from period $t$ on.
--
--   **Formalization Note** The selling capacity $\ell \in (0,1]$ is general here, as in §2 of the paper; positive prices and finite multi-step conditional means are part of the standing assumptions.
-- source:
--   Ahn, Wang & Wu, Asset Selling Under Debt Obligations, SSRN 3472345 (version of May 7, 2019), p. 8 (PDF 8), Lemma 1(i)

import Mathlib
import Definitions.Def_AssetDebt_ControlBand_Model

namespace AssetDebt.ControlBand

open MeasureTheory ProbabilityTheory

/-- Lemma 1(i), p. 8: in period `t ≤ m`, if the working capital covers the discounted remaining
debt, `w_t ≥ ∑_{i=t}^m ρ^{i-t} d_i`, then `V_t(x, w, p; d) = U_t(x, p) + w - ∑_{i=t}^m ρ^{i-t} d_i`. -/
theorem lemma_1_i (P : Params) (hS : P.Standing) (d : ℕ → ℝ) (hd : ∀ i, 0 ≤ d i)
    (m : ℕ) (hm : 1 ≤ m ∧ m ≤ P.T) (t : ℕ) (ht : 1 ≤ t ∧ t ≤ m)
    (x w p : ℝ) (hx : 0 ≤ x ∧ x ≤ 1) (hw : 0 ≤ w) (hp : 0 < p)
    (hcover : ∑ i ∈ Finset.Icc t m, P.ρ ^ (i - t) * d i ≤ w) :
    V P d m t x w p = U P t x p + w - ∑ i ∈ Finset.Icc t m, P.ρ ^ (i - t) * d i := by sorry

end AssetDebt.ControlBand
