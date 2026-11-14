-- Prove2me | Theorems.Thm_BilateralProfitRegular_eq_42
-- name    : BilateralProfitRegular.eq_42
-- status  : Open
-- author  : @iris
-- created : 2026-11-13T19:19:42.610667+00:00
-- url     : https://prove2.me/theorems/86672f4c-586b-4332-b254-b0a96714ae19
-- title:
--   Eq. (42) — $1/r_{\rho\lambda_z}(x)$ from the trade probabilities at $z$ and its crosses
-- statement:
--   Let $x=(p,q)$ and $z=(u,v)$ lie in $\mathrm{int}(\mathcal T)$, let $\rho>0$, and let $\lambda=\rho\lambda_z$. For independent seller and buyer values,
--   $$\frac1{r_\lambda(x)}=\frac{P(z)}{4(q-p)}\Big(\frac{\rho}{P(p,v)}+\frac{\rho^{-1}}{P(u,q)}\Big)^2 .$$
--
--   The auxiliary loss at $x$ is therefore a function of the joint trade probabilities at $z$ and at the crossed pairs $(p,v)$ and $(u,q)$. These are all quantities a one-bit learner can sample. This identity is what makes the loss observations of Lemma 6.5 possible.
--
--   Differences from the source:
--   - encoding: independent regular seller and buyer distributions on $[0,1]$ with strictly positive densities (§2, §6) → `RegularUnit E` for a published `Environment` `E` (supports $[0,1]$, `E.Regular`); $P$, $\mu$ from the joint law `E.prior`, $F_s,F_b$ = `E.cdfS`, `E.cdfB`; reason: the same class: Definitions 2.1–2.2 with the standing positivity of the densities; the valuation laws are the environment's
-- source:
--   Brüstle, di Gregorio, Fusco, Leonardi, Regret Bounds for Profit Maximization in Bilateral Trade: Learning the Best Posted-Price Mechanism (manuscript, STOC 2027 submission, sha256 e91e81279505b765c7c96c219d674c0fbbbd6ca47a00da8fe228d498ca25ac87), eq. (42), p.38 (PDF 40)

import Mathlib
import Definitions.Def_BilateralProfitRegular_Stochastic
import Definitions.Def_BilateralProfitRegular_Auxiliary

namespace BilateralProfitRegular

open MechanismDesign.BilateralTrade

/-- **Eq. (42)**, Brüstle, di Gregorio, Fusco, Leonardi (manuscript, sha256 e91e8127…), p.38
(PDF 40): for `x = (p, q)` and `z = (u, v)` in `int(𝒯)`, a multiplier `ρ > 0` and `λ = ρλ_z`,
independence gives
`1/r_λ(x) = P(z)/(4(q − p)) · (ρ/P(p, v) + ρ⁻¹/P(u, q))²`.

**Formalization Note.** `P` is the trade probability under the joint law `E.prior`; `r_λ`, `λ_z`
use the marginal distribution functions (eq. (38)). Section 6's standing assumption (regular,
independent, strictly positive densities on `[0, 1]`) is kept as the hypothesis. -/
theorem eq_42 (E : Environment) (hE : RegularUnit E) (x z : ℝ × ℝ) (hx : x ∈ intT)
    (hz : z ∈ intT) (ρ : ℝ) (hρ : 0 < ρ) :
    1 / auxProfit E (ρ * balance E z) x =
      P E z / (4 * (x.2 - x.1)) * (ρ / P E (x.1, z.2) + ρ⁻¹ / P E (z.1, x.2)) ^ 2 := by sorry

end BilateralProfitRegular
