-- Prove2me | Theorems.Thm_AssetDebt_ControlBand_lemma_1_ii
-- name    : AssetDebt.ControlBand.lemma_1_ii
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-19T01:14:03.017999+00:00
-- url     : https://prove2.me/theorems/a3d98006-fc41-4a95-aca1-0975cd21017f
-- title:
--   Lemma 1(ii), p. 8 — with no asset left, the equity value is $(w_t - \sum_{i=t}^m \rho^{i-t} d_i)^+$
-- statement:
--   Consider a debt schedule $d = (d_i)$ with $d_i \ge 0$ and maturity $m$, $1 \le m \le T$, and a period $1 \le t \le m$. When the asset is sold out ($x = 0$), with working capital $w \ge 0$ and price $p > 0$,
--
--   $$V_t(0, w, p; d) \;=\; \Big( w - \sum_{i=t}^{m} \rho^{\,i-t} d_i \Big)^+ .$$
--
--   A seller with no asset either has enough working capital to pay all remaining installments, and keeps the discounted surplus, or goes bankrupt with equity value zero.
--
--   **Formalization Note** The positive part is written as $\max(\cdot, 0)$; the capacity $\ell$ is general.
-- source:
--   Ahn, Wang & Wu, Asset Selling Under Debt Obligations, SSRN 3472345 (version of May 7, 2019), p. 8 (PDF 8), Lemma 1(ii)

import Mathlib
import Definitions.Def_AssetDebt_ControlBand_Model

namespace AssetDebt.ControlBand

open MeasureTheory ProbabilityTheory

/-- Lemma 1(ii), p. 8: in period `t ≤ m`, with no asset left,
`V_t(0, w, p; d) = (w - ∑_{i=t}^m ρ^{i-t} d_i)^+`. -/
theorem lemma_1_ii (P : Params) (hS : P.Standing) (d : ℕ → ℝ) (hd : ∀ i, 0 ≤ d i)
    (m : ℕ) (hm : 1 ≤ m ∧ m ≤ P.T) (t : ℕ) (ht : 1 ≤ t ∧ t ≤ m)
    (w p : ℝ) (hw : 0 ≤ w) (hp : 0 < p) :
    V P d m t 0 w p = max (w - ∑ i ∈ Finset.Icc t m, P.ρ ^ (i - t) * d i) 0 := by sorry

end AssetDebt.ControlBand
