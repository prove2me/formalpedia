-- Prove2me | Theorems.Thm_BilateralProfitRegular_lemma_6_2
-- name    : BilateralProfitRegular.lemma_6_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-13T19:19:29.943209+00:00
-- url     : https://prove2.me/theorems/d178c3fd-8c51-476f-a1d9-27dda3aed536
-- title:
--   Lemma 6.2 — auxiliary profits: $1/r_\lambda$ is convex, $r_\lambda=\mu\,\mathrm{sech}^2(\log(\lambda/\lambda_x))$, and stability (40)
-- statement:
--   Let the seller and buyer distributions be independent and regular on $[0,1]$, with strictly positive densities. Let $\lambda>0$, let $r_\lambda$ be the auxiliary profit and $\lambda_x$ the balancing parameter of eq. (38). Then:
--
--   1. $x\mapsto 1/r_\lambda(x)$ is convex on $\mathrm{int}(\mathcal T)$.
--   2. With $\mathrm{sech}(t)=2/(e^t+e^{-t})$, for every $x\in\mathrm{int}(\mathcal T)$,
--   $$r_\lambda(x)=\mu(x)\,\mathrm{sech}^2\Big(\log\frac{\lambda}{\lambda_x}\Big),\qquad 0\le\mu(x)-r_\lambda(x)\le\mu(x)\Big(\log\frac{\lambda}{\lambda_x}\Big)^2 .$$
--   3. In particular, $0<r_\lambda(x)\le\mu(x)$ and $r_{\lambda_x}(x)=\mu(x)$.
--   4. For every $\theta\in\mathbb R$,
--   $$\mu^\star-r_{\lambda e^\theta}(x)\le2\big(\mu^\star-r_\lambda(x)\big)+2\mu^\star\theta^2 .$$
--
--   The lemma explains why the algorithm optimizes the convex reciprocals $1/r_\lambda$ in place of the profit: $r_\lambda$ matches $\mu$ at the balancing parameter, and it degrades only quadratically in the log-error of $\lambda$.
--
--   Differences from the source:
--   - encoding: independent regular seller and buyer distributions on $[0,1]$ with strictly positive densities (§2, §6) → `RegularUnit E` for a published `Environment` `E` (supports $[0,1]$, `E.Regular`); $P$, $\mu$ from the joint law `E.prior`, $F_s,F_b$ = `E.cdfS`, `E.cdfB`; reason: the same class: Definitions 2.1–2.2 with the standing positivity of the densities; the valuation laws are the environment's
-- source:
--   Brüstle, di Gregorio, Fusco, Leonardi, Regret Bounds for Profit Maximization in Bilateral Trade: Learning the Best Posted-Price Mechanism (manuscript, STOC 2027 submission, sha256 e91e81279505b765c7c96c219d674c0fbbbd6ca47a00da8fe228d498ca25ac87), Lemma 6.2, p.37 (PDF 39)

import Mathlib
import Definitions.Def_BilateralProfitRegular_Stochastic
import Definitions.Def_BilateralProfitRegular_Auxiliary

namespace BilateralProfitRegular

open MechanismDesign.BilateralTrade

/-- **Lemma 6.2 (Auxiliary profits)**, Brüstle, di Gregorio, Fusco, Leonardi (manuscript, sha256
e91e8127…), p.37 (PDF 39). For independent regular seller and buyer distributions on `[0, 1]` with
strictly positive densities and every `λ > 0`: `x ↦ 1/r_λ(x)` is convex on `int(𝒯)`; for every
`x ∈ int(𝒯)`, `r_λ(x) = µ(x) sech²(log(λ/λ_x))` with `sech t = 2/(e^t + e^{−t})` and
`0 ≤ µ(x) − r_λ(x) ≤ µ(x) (log(λ/λ_x))²` (39); in particular `0 < r_λ(x) ≤ µ(x)` and
`r_{λ_x}(x) = µ(x)`; and for every `θ ∈ ℝ`, `µ⋆ − r_{λe^θ}(x) ≤ 2(µ⋆ − r_λ(x)) + 2µ⋆θ²` (40).

**Formalization Note.** `r_λ`, `λ_x` are eq. (38) with `F_s = E.cdfS`, `F_b = E.cdfB`; `µ` is
computed from the joint law `E.prior`; `µ⋆` is the supremum of `µ` over `[0,1]²`. Logarithms are
natural. -/
theorem lemma_6_2 (E : Environment) (hE : RegularUnit E) (lam : ℝ) (hlam : 0 < lam) :
    ConvexOn ℝ intT (fun x => 1 / auxProfit E lam x) ∧
    ∀ x ∈ intT,
      auxProfit E lam x =
          mu E x * (2 / (Real.exp (Real.log (lam / balance E x)) +
            Real.exp (-Real.log (lam / balance E x)))) ^ 2 ∧
        0 ≤ mu E x - auxProfit E lam x ∧
        mu E x - auxProfit E lam x ≤ mu E x * Real.log (lam / balance E x) ^ 2 ∧
        0 < auxProfit E lam x ∧ auxProfit E lam x ≤ mu E x ∧
        auxProfit E (balance E x) x = mu E x ∧
        ∀ θ : ℝ, muStar E - auxProfit E (lam * Real.exp θ) x ≤
          2 * (muStar E - auxProfit E lam x) + 2 * muStar E * θ ^ 2 := by sorry

end BilateralProfitRegular
