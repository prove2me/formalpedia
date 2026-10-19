-- Prove2me | Theorems.Thm_AssetDebt_ControlBand_eq_A_6
-- name    : AssetDebt.ControlBand.eq_A_6
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-19T01:13:58.696275+00:00
-- url     : https://prove2.me/theorems/2a22025c-edd9-412b-9ae6-b3e4b795a998
-- title:
--   (A.6), proof of Lemma 3, Online Appendix p. 5 — equity value at maturity: $V_m = \max\{p_m, R^o_m\}(x_m - (d_m - w_m)/p_m)^+$ for $w_m \le d_m$
-- statement:
--   Assume no capacity constraint ($\ell = 1$) and a single debt payment $D$ due at the end of period $m$, with $1 \le m < T$. At maturity, for inventory $x \in [0,1]$, working capital $0 \le w \le D$ and price $p > 0$,
--
--   $$V_m(x, w, p; d) \;=\; \max\{p,\ R^o_m\}\Big( x - \frac{D - w}{p} \Big)^+ .$$
--
--   The seller must sell at least $(D - w)/p$ to pay the debt; if that exceeds the inventory the firm is bankrupt and its equity is zero, and otherwise the remaining asset is valued at the debt-free rate $\max\{p, R^o_m\}$ per unit.
--
--   **Formalization Note** The positive part is written as $\max(\cdot, 0)$.
-- source:
--   Ahn, Wang & Wu, Asset Selling Under Debt Obligations, SSRN 3472345 (version of May 7, 2019), Online Appendix p. 5 (PDF 37), proof of Lemma 3, eq. (A.6)

import Mathlib
import Definitions.Def_AssetDebt_ControlBand_Model

namespace AssetDebt.ControlBand

open MeasureTheory ProbabilityTheory

/-- (A.6), proof of Lemma 3, Online Appendix p. 5: under a single payment `D = d_m` at
`m < T` and `ℓ = 1`, for `w_m ≤ d_m`,
`V_m(x, w, p; d) = max{p, R^o_m} (x - (d_m - w)/p)^+`. -/
theorem eq_A_6 (P : Params) (hS : P.Standing) (hℓ : P.ℓ = 1)
    (m : ℕ) (hm : 1 ≤ m ∧ m < P.T) (D : ℝ)
    (x w p : ℝ) (hx : 0 ≤ x ∧ x ≤ 1) (hw : 0 ≤ w) (hwD : w ≤ D) (hp : 0 < p) :
    V P (singlePayment m D) m m x w p = max p (Ro P m p) * max (x - (D - w) / p) 0 := by sorry

end AssetDebt.ControlBand
