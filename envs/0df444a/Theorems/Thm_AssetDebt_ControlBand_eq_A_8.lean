-- Prove2me | Theorems.Thm_AssetDebt_ControlBand_eq_A_8
-- name    : AssetDebt.ControlBand.eq_A_8
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-19T01:14:00.732725+00:00
-- url     : https://prove2.me/theorems/8a27ef85-0641-4108-8b67-84ab9b5db691
-- title:
--   (A.8), proof of Lemma 3, Online Appendix p. 6 — for $t < m$ and $w_t \le \rho^{m-t} d_m$, $V_t$ is the max of the values of selling nothing, the debt-covering quantity, or everything
-- statement:
--   Assume no capacity constraint ($\ell = 1$) and a single debt payment $D = d_m$ due at the end of period $m$, with $1 \le m < T$. For a period $1 \le t < m$, inventory $x \in [0,1]$, working capital $0 \le w \le \rho^{m-t} D$ and price $p > 0$,
--
--   $$V_t(x, w, p; d) = \max\Big\{ \rho\, E_t V_{t+1}\big(x,\ \rho^{-1} w,\ P_{t+1}; d\big),\ \ R^o_t\Big(x - \frac{\rho^{m-t} D - w}{p}\Big),\ \ w + p\,x - \rho^{m-t} D \Big\}.$$
--
--   The three terms are the values of selling nothing, of selling exactly the quantity $(\rho^{m-t}D - w)/p$ whose revenue secures the debt, and of selling the whole inventory.
-- source:
--   Ahn, Wang & Wu, Asset Selling Under Debt Obligations, SSRN 3472345 (version of May 7, 2019), Online Appendix p. 6 (PDF 38), proof of Lemma 3, eq. (A.8)

import Mathlib
import Definitions.Def_AssetDebt_ControlBand_Model

namespace AssetDebt.ControlBand

open MeasureTheory ProbabilityTheory

/-- (A.8), proof of Lemma 3, Online Appendix p. 6: under a single payment `d_m = D` at
`m < T` and `ℓ = 1`, for `t < m` and `w ≤ ρ^{m-t} d_m`,
`V_t(x, w, p; d) = max{ρ E_t V_{t+1}(x, ρ⁻¹ w, P_{t+1}; d), R^o_t (x - (ρ^{m-t} d_m - w)/p),
w + p x - ρ^{m-t} d_m}`. -/
theorem eq_A_8 (P : Params) (hS : P.Standing) (hℓ : P.ℓ = 1)
    (m : ℕ) (hm : 1 ≤ m ∧ m < P.T) (D : ℝ) (t : ℕ) (ht : 1 ≤ t ∧ t < m)
    (x w p : ℝ) (hx : 0 ≤ x ∧ x ≤ 1) (hw : 0 ≤ w) (hwD : w ≤ P.ρ ^ (m - t) * D) (hp : 0 < p) :
    V P (singlePayment m D) m t x w p =
      max (max (P.ρ * ∫ p', V P (singlePayment m D) m (t + 1) x (P.ρ⁻¹ * w) p' ∂(P.κ t p))
               (Ro P t p * (x - (P.ρ ^ (m - t) * D - w) / p)))
          (w + p * x - P.ρ ^ (m - t) * D) := by sorry

end AssetDebt.ControlBand
