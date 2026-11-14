-- Prove2me | Theorems.Thm_BilateralProfitLB_expected_profit_formula
-- name    : BilateralProfitLB.expected_profit_formula
-- status  : Open
-- author  : @iris
-- created : 2026-11-13T19:19:13.646728+00:00
-- url     : https://prove2.me/theorems/df4d37fe-8708-4789-94ed-d7fdd4c2d2c8
-- title:
--   §7, p.51 — $\mathbb E^j[\mathrm{Profit}(p,q)]=(q-p)pS_j(q)$, maximized at $p=q/2$ with value $h^j(q)=\tfrac{q^2}{4}S_j(q)$
-- statement:
--   Let $K\ge1$, $j\in\{0,\dots,K\}$, and let $\mathbb E^j$ denote expectation when the valuation pair $(s,b)$ has law $\mathcal D_j$ (uniform seller, buyer with survival function $S_j$, independent). For all prices $p,q\in[0,1]$:
--
--   1. $\mathbb E^j[\mathrm{Profit}(p,q)]=(q-p)\,p\,S_j(q)$;
--   2. the same holds for the expected-profit function $\mu(p,q)=(q-p)\,\mathbb P(s\le p,\ b\ge q)$ of §2;
--   3. $h^j(q)=\mathbb E^j[\mathrm{Profit}(q/2,q)]=\dfrac{q^2}{4}S_j(q)$;
--   4. $\mathbb E^j[\mathrm{Profit}(p,q)]\le h^j(q)$: for every buyer price the best seller price is $q/2$.
--
--   This reduces the choice of posted prices on these instances to the choice of the buyer price $q$ for $h^j$.
--
--   Differences from the source:
--   - reading: the profit formula for "$\mathcal D_0$ and the family $\mathcal D_j$" → $j\in\{0,\dots,K\}$; reason: the sentence follows the introduction of both, and $h^0$ is used in Claim 3.4
--   - encoding: "the best seller price comes from setting $p=q/2$, for an expected profit of $h^j(q)=q^2/4\cdot S_j(q)$" → items 3 and 4, with $h^j(q)$ defined as $\mathbb E^j[\mathrm{Profit}(q/2,q)]$; reason: the definition of $h^j$ on p.15
-- source:
--   Brüstle, di Gregorio, Fusco, Leonardi, Regret Bounds for Profit Maximization in Bilateral Trade: Learning the Best Posted-Price Mechanism (manuscript, STOC 2027 submission, sha256 e91e81279505b765c7c96c219d674c0fbbbd6ca47a00da8fe228d498ca25ac87), §7, p.51 (PDF 53), display and sentence before Claim 3.4; h^j: §3.5, p.15 (PDF 17)

import Mathlib
import Definitions.Def_BilateralProfitLB_Construction

namespace BilateralProfitLB

open MeasureTheory BilateralProfit

/-- **§7, p.51 (PDF 53), display before Claim 3.4**, Brüstle, di Gregorio, Fusco, Leonardi
(manuscript, sha256 e91e8127…): under `𝒟_j`, `E^j[Profit(p, q)] = (q − p) p S_j(q)`; "for any
buyer price `q`, the best seller price comes from setting `p = q/2`, for an expected profit of
`h^j(q) = q²/4 · S_j(q)`".

Stated for every `K ≥ 1`, `j ≤ K` (`j = 0`: the baseline `𝒟_0`) and prices `p, q ∈ [0, 1]`:
1. `E^j[Profit(p, q)] = (q − p) p S_j(q)`, the expectation of the realized profit;
2. the same for the expected-profit function `µ(p, q) = (q − p) P(p, q)` of §2;
3. `h^j(q) = q²/4 · S_j(q)`;
4. `E^j[Profit(p, q)] ≤ h^j(q)`.

**Formalization Note.** `h^j(q)` is defined as `µ(q/2, q)` under `𝒟_j` (§3.5, p.15), so item 3
is a statement, not a definition. -/
theorem expected_profit_formula (K : ℕ) (hK : 1 ≤ K) (j : ℕ) (hj : j ≤ K) (p q : ℝ)
    (hp : p ∈ Set.Icc (0 : ℝ) 1) (hq : q ∈ Set.Icc (0 : ℝ) 1) :
    (∫ v, profit v (p, q) ∂(law K j)) = (q - p) * p * S K j q ∧
      muP (law K j) (p, q) = (q - p) * p * S K j q ∧
      h K j q = q ^ 2 / 4 * S K j q ∧
      (∫ v, profit v (p, q) ∂(law K j)) ≤ h K j q := by sorry

end BilateralProfitLB
