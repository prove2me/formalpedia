-- Prove2me | Theorems.Thm_AssetDebt_ControlBand_footnote_4
-- name    : AssetDebt.ControlBand.footnote_4
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-19T01:14:03.69548+00:00
-- url     : https://prove2.me/theorems/ae944418-9151-4b04-92ba-21209cb98c61
-- title:
--   Footnote 4, Online Appendix p. 7 — the denominator of $R^{(1)}_t$ is positive: $0 \le \rho E_t V_{t+1} < R^o_t$
-- statement:
--   Assume no capacity constraint ($\ell = 1$) and a single debt payment $D > 0$ due at the end of period $m$, with $1 \le m < T$. For every period $1 \le t \le m$ and every current price $p > 0$,
--
--   $$0 \;\le\; \rho\, E_t V_{t+1}(1, 0, P_{t+1}; d) \;<\; R^o_t, \qquad\text{and}\qquad R^o_t > 0 .$$
--
--   In particular the denominator $R^o_t - \rho E_t V_{t+1}$ in the definition of the critical price $R^{(1)}_t$ is strictly positive: any debt strictly reduces the firm's value.
--
--   **Formalization Note** The footnote's own reason ("any debt reduces the firm's value") gives only a weak inequality; the strict inequality uses $D > 0$ and the standing assumption of almost surely positive prices. The clause $R^o_t > 0$ is added; it is needed at $t = m$, where $\rho E_m V_{m+1} = 0$.
-- source:
--   Ahn, Wang & Wu, Asset Selling Under Debt Obligations, SSRN 3472345 (version of May 7, 2019), Online Appendix p. 7 (PDF 39), proof of Proposition 4, footnote 4

import Mathlib
import Definitions.Def_AssetDebt_ControlBand_Model

namespace AssetDebt.ControlBand

open MeasureTheory ProbabilityTheory

/-- Footnote 4, proof of Proposition 4, Online Appendix p. 7: under a single payment
`d_m = D > 0` at `m < T` and `ℓ = 1`, for `t ≤ m` the denominator of `R^{(1)}_t` is positive:
`0 ≤ ρ E_t V_{t+1}(1, 0, P_{t+1}; d) < R^o_t`; moreover `R^o_t > 0`. -/
theorem footnote_4 (P : Params) (hS : P.Standing) (hℓ : P.ℓ = 1)
    (m : ℕ) (hm : 1 ≤ m ∧ m < P.T) (D : ℝ) (hD : 0 < D) (t : ℕ) (ht : 1 ≤ t ∧ t ≤ m)
    (p : ℝ) (hp : 0 < p) :
    0 ≤ C P m D t p ∧ C P m D t p < Ro P t p ∧ 0 < Ro P t p := by sorry

end AssetDebt.ControlBand
