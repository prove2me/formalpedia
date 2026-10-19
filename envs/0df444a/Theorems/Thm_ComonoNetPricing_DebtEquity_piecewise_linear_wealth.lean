-- Prove2me | Theorems.Thm_ComonoNetPricing_DebtEquity_piecewise_linear_wealth
-- name    : ComonoNetPricing.DebtEquity.piecewise_linear_wealth
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-19T04:16:27.185452+00:00
-- url     : https://prove2.me/theorems/679e2bbb-472e-41db-b77a-4d5713645475
-- title:
--   §3.1 display, p. 11 — V(x) = Δ(I{V(x)<0})x − δ(I{V(x)<0}) for every endowment x ∈ ℝⁿ₊
-- statement:
--   For a positive integer $n$, consider the Rogers–Veraart network under the standing assumptions, with greatest clearing wealth $V(x)$ and the matrices $\Delta(z)$, $\delta(z)$ of (3)–(4). For every endowment $x \in \mathbb R^n_+$, with $z = \mathbb I_{\{V(x)<0\}}$ the indicator of the defaulting banks,
--   $$V(x) = \Delta(z)\,x - \delta(z).$$
--
--   Once the default set is known, the clearing wealths are an explicit affine function of the endowments. Theorem 3.6 integrates this formula over the intervals of the factor on which the default set is constant.
--
--   **Formalization Note** The page writes this with ":=" but it is an identity "by construction", since $V$ is already defined in Definition 2.2. The default set is the `Finset` of banks with $V_i(x) < 0$.
-- source:
--   Banerjee & Feinstein, Pricing of debt and equity in a financial network with comonotonic endowments, arXiv:1810.01372v5, p. 11, §3.1 display following (3)–(4)

import Mathlib
import Definitions.Def_ComonoNetPricing_DebtEquity_Network
import Definitions.Def_ComonoNetPricing_DebtEquity_Model

namespace ComonoNetPricing.DebtEquity

open Matrix

/-- §3.1 display, p. 11: for every endowment `x ∈ ℝⁿ₊`, the greatest clearing wealth is
`V(x) = Δ(1{V(x) < 0}) x − δ(1{V(x) < 0})` with `Δ`, `δ` of (3)–(4). -/
theorem piecewise_linear_wealth {n : ℕ} (hn : 0 < n) (N : Network n) (hN : N.Standing) (x : Fin n → ℝ)
    (hx : 0 ≤ x) :
    N.clearingWealth x =
      N.DeltaM (Finset.univ.filter (fun i => N.clearingWealth x i < 0)) *ᵥ x
        - N.deltaV (Finset.univ.filter (fun i => N.clearingWealth x i < 0)) := by sorry

end ComonoNetPricing.DebtEquity
