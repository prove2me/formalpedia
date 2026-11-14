-- Prove2me | Theorems.Thm_BilateralProfitRegular_eq_47
-- name    : BilateralProfitRegular.eq_47
-- status  : Open
-- author  : @iris
-- created : 2026-11-13T19:19:50.643676+00:00
-- url     : https://prove2.me/theorems/1e3fc4b5-72e9-426f-ad00-824219273838
-- title:
--   Eq. (47) — ratios of balancing parameters from crossed trade probabilities
-- statement:
--   For $x=(p,q)$ and $z=(u,v)$ in $\mathrm{int}(\mathcal T)$ and independent seller and buyer values,
--   $$\log\frac{\lambda_x}{\lambda_z}=\frac12\log\frac{P(p,v)}{P(u,q)} .$$
--
--   The balancing parameters themselves depend on the unknown marginals. Their ratios, however, can be estimated from trade bits at the crossed pairs. Algorithm 7 groups prices with this identity, and the calibration of Lemma 6.5 relies on it.
--
--   Differences from the source:
--   - encoding: "for $x=(p,q)$ and $z=(u,v)$" → $x,z\in\mathrm{int}(\mathcal T)$; reason: $\lambda_x,\lambda_z$ are defined (eq. (38)) only there; this only excludes undefined cases
--   - encoding: independent regular seller and buyer distributions on $[0,1]$ with strictly positive densities (§2, §6) → `RegularUnit E` for a published `Environment` `E` (supports $[0,1]$, `E.Regular`); $P$, $\mu$ from the joint law `E.prior`, $F_s,F_b$ = `E.cdfS`, `E.cdfB`; reason: the same class: Definitions 2.1–2.2 with the standing positivity of the densities; the valuation laws are the environment's
-- source:
--   Brüstle, di Gregorio, Fusco, Leonardi, Regret Bounds for Profit Maximization in Bilateral Trade: Learning the Best Posted-Price Mechanism (manuscript, STOC 2027 submission, sha256 e91e81279505b765c7c96c219d674c0fbbbd6ca47a00da8fe228d498ca25ac87), eq. (47), p.39 (PDF 41)

import Mathlib
import Definitions.Def_BilateralProfitRegular_Stochastic
import Definitions.Def_BilateralProfitRegular_Auxiliary

namespace BilateralProfitRegular

open MechanismDesign.BilateralTrade

/-- **Eq. (47)**, Brüstle, di Gregorio, Fusco, Leonardi (manuscript, sha256 e91e8127…), p.39
(PDF 41): for `x = (p, q)` and `z = (u, v)`, independence gives
`log(λ_x/λ_z) = ½ log(P(p, v)/P(u, q))`.

**Formalization Note.** Stated for `x, z ∈ int(𝒯)`, where `λ_x, λ_z` are defined and the four
trade probabilities are positive (also when `p > v`). Section 6's standing assumption (regular,
independent, strictly positive densities on `[0, 1]`) is kept. Natural logarithms. -/
theorem eq_47 (E : Environment) (hE : RegularUnit E) (x z : ℝ × ℝ) (hx : x ∈ intT)
    (hz : z ∈ intT) :
    Real.log (balance E x / balance E z) =
      1 / 2 * Real.log (P E (x.1, z.2) / P E (z.1, x.2)) := by sorry

end BilateralProfitRegular
