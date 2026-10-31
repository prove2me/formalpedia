-- Prove2me | Theorems.Thm_CommodityCPC_kappa_pos
-- name    : CommodityCPC.kappa_pos
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T02:51:40.528872+00:00
-- url     : https://prove2.me/theorems/332513b6-ca03-4142-bc92-64eb64360d95
-- title:
--   §4.1 — $\kappa>0$
-- statement:
--   Under the standing assumptions, the denominator of $\kappa=1/[4-\gamma^2\lambda_A\lambda_B(1+\beta)^2]$ is positive, and hence
--
--   $$
--   \kappa>0.
--   $$
--
--   The constant $\kappa$ appears in every equilibrium quantity and every equilibrium profit of the model. Its positivity is what makes the linear system of equilibrium signal coefficients uniquely solvable.
--
--   Differences from the source:
--   - encoding: κ > 0 → both the denominator of κ and κ are positive; reason: in Lean 1/0 = 0, and the two claims are equivalent; the denominator is stated so that the division is visibly safe
-- source:
--   Xing–Liu–Zhang–Zhao, SSRN 4717149 (2023-12-27), §4.1, p. 12; version of record: Management Science (2024), doi:10.1287/mnsc.2023.00304

import Mathlib
import Definitions.Def_CommodityCPC_Model

namespace CommodityCPC

/-- **`κ > 0`**, Xing–Liu–Zhang–Zhao, *The Bright Side of Price Volatility in Global Commodity
Procurement*, SSRN 4717149 (2023-12-27), Management Science (2024),
doi:10.1287/mnsc.2023.00304, §4.1, p. 12: the denominator `4 − γ²λ_Aλ_B(1 + β)²` of
`κ ≡ 1/[4 − γ²λ_Aλ_B(1 + β)²]` is positive, and hence so is `κ`.

**Formalization Note.** The denominator is stated as well, so that the division in `κ` is
visibly safe. -/
theorem kappa_pos (p : Params) :
    0 < 4 - p.γ ^ 2 * p.lam .A * p.lam .B * (1 + p.β) ^ 2 ∧ 0 < p.κ := by sorry

end CommodityCPC
