-- Prove2me | Theorems.Thm_BilateralProfitRegular_lemma_6_3
-- name    : BilateralProfitRegular.lemma_6_3
-- status  : Open
-- author  : @iris
-- created : 2026-11-13T19:19:35.052341+00:00
-- url     : https://prove2.me/theorems/290c2a35-e70f-4fa7-9767-a3fcbfbcad46
-- title:
--   Lemma 6.3 — crossed prices of two high-auxiliary-profit pairs are in $\mathcal T$, nearly optimal, with comparable trade probabilities
-- statement:
--   Let $\lambda>0$. Suppose $x=(p,q)$ and $z=(u,v)$ in $\mathrm{int}(\mathcal T)$ satisfy $r_\lambda(x),r_\lambda(z)\ge0.99\mu^\star$. Then:
--
--   1. $(p,v)\in\mathcal T$ and $(u,q)\in\mathcal T$;
--   2. each crossed pair $y\in\{(p,v),(u,q)\}$ satisfies
--   $$\mu^\star-\mu(y)\le4\big(\mu^\star-r_\lambda(x)+\mu^\star-r_\lambda(z)\big);$$
--   3. the four trade probabilities $P(x),P(z),P(p,v),P(u,q)$ are within a factor of $3$ of each other.
--
--   The lemma ensures that the crossed queries needed to estimate $r_\lambda$ through eq. (42) are themselves cheap in regret.
--
--   Differences from the source:
--   - reading: "either crossed pair $y$ satisfies" → both crossed pairs satisfy the bound; reason: the proof (46) bounds each crossed pair; "either" means "each"
--   - reading: "the four trade probabilities are within a factor of 3 of each other" → $P(a)\le3P(b)$ for any two $a,b$ of the four pairs; reason: the proof shows $\max P/\min P<3$
--   - encoding: independent regular seller and buyer distributions on $[0,1]$ with strictly positive densities (§2, §6) → `RegularUnit E` for a published `Environment` `E` (supports $[0,1]$, `E.Regular`); $P$, $\mu$ from the joint law `E.prior`, $F_s,F_b$ = `E.cdfS`, `E.cdfB`; reason: the same class: Definitions 2.1–2.2 with the standing positivity of the densities; the valuation laws are the environment's
-- source:
--   Brüstle, di Gregorio, Fusco, Leonardi, Regret Bounds for Profit Maximization in Bilateral Trade: Learning the Best Posted-Price Mechanism (manuscript, STOC 2027 submission, sha256 e91e81279505b765c7c96c219d674c0fbbbd6ca47a00da8fe228d498ca25ac87), Lemma 6.3, p.38 (PDF 40); proof pp.38–39 (PDF 40–41)

import Mathlib
import Definitions.Def_BilateralProfitRegular_Stochastic
import Definitions.Def_BilateralProfitRegular_Auxiliary

namespace BilateralProfitRegular

open MechanismDesign.BilateralTrade

/-- **Lemma 6.3 (Crossed prices)**, Brüstle, di Gregorio, Fusco, Leonardi (manuscript, sha256
e91e8127…), p.38 (PDF 40). If `x = (p, q)` and `z = (u, v)` in `int(𝒯)` satisfy
`r_λ(x), r_λ(z) ≥ 0.99µ⋆`, then `(p, v)` and `(u, q)` belong to `𝒯`, either crossed pair `y`
satisfies `µ⋆ − µ(y) ≤ 4(µ⋆ − r_λ(x) + µ⋆ − r_λ(z))`, and the four trade probabilities
`P(x), P(z), P(p, v), P(u, q)` are within a factor of `3` of each other.

**Formalization Note.** "Either crossed pair" is read as "each of the two crossed pairs" (the
proof bounds both). "Within a factor of 3": `P(a) ≤ 3 P(b)` for any two of the four pairs.
Stated for every `λ > 0`. -/
theorem lemma_6_3 (E : Environment) (hE : RegularUnit E) (lam : ℝ) (hlam : 0 < lam)
    (x z : ℝ × ℝ) (hx : x ∈ intT) (hz : z ∈ intT)
    (hrx : 99 / 100 * muStar E ≤ auxProfit E lam x)
    (hrz : 99 / 100 * muStar E ≤ auxProfit E lam z) :
    (x.1, z.2) ∈ triT ∧ (z.1, x.2) ∈ triT ∧
    muStar E - mu E (x.1, z.2) ≤
      4 * (muStar E - auxProfit E lam x + (muStar E - auxProfit E lam z)) ∧
    muStar E - mu E (z.1, x.2) ≤
      4 * (muStar E - auxProfit E lam x + (muStar E - auxProfit E lam z)) ∧
    ∀ a ∈ ({x, z, (x.1, z.2), (z.1, x.2)} : Set (ℝ × ℝ)),
      ∀ b ∈ ({x, z, (x.1, z.2), (z.1, x.2)} : Set (ℝ × ℝ)), P E a ≤ 3 * P E b := by sorry

end BilateralProfitRegular
