-- Prove2me | Theorems.Thm_DistFreePricing_Maximin_theorem_2
-- name    : DistFreePricing.Maximin.theorem_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-23T03:55:39.342051+00:00
-- url     : https://prove2.me/theorems/54ed3507-63af-46b1-92fb-4b25fd495c03
-- title:
--   Theorem 2, p. 11 — p* = µ − k*σ is maximin-optimal with worst-case profit L and earns at least ρ·max_p π(p;F) for every F ∈ 𝓕
-- statement:
--   **Robust price and performance guarantee.** A seller with constant marginal cost $c\ge0$ knows only the mean $\mu\ge c$, $\mu>0$, and the standard deviation $\sigma>0$ of the customers' valuation $V\ge0$. Let $\mathscr F$ be the class of all valuation laws on $[0,\infty)$ with these two moments, and $\pi(p;F)=(p-c)\,\mathbb P_F(V\ge p)$ the profit of a posted price $p$. Put
--
--   $$\tau=\frac{\mu-c}{\sigma},\quad \gamma=\frac{c}{\mu},\quad k^*=\sqrt[3]{\tau+\sqrt{\tau^2+1}}+\sqrt[3]{\tau-\sqrt{\tau^2+1}},\quad p^*=\mu-k^*\sigma,$$
--
--   $$L=(\mu-c)\Big(1-\frac{3}{2\tau}k^*\Big),\qquad \rho=\frac{1-\frac{3}{2\tau}k^*}{1+\frac{\gamma}{(1-\gamma)(1+\tau^2)}} .$$
--
--   Then $k^*\ge0$, and:
--
--   1. $\pi(p^*;F)\ge L$ for every $F\in\mathscr F$;
--   2. no price does better in the worst case: for every real price $p$ and every $\epsilon>0$ there is $F\in\mathscr F$ with $\pi(p;F)<L+\epsilon$;
--   3. if $c<\mu$ (so that $\rho$ is defined), then for every $F\in\mathscr F$ and every price $p$, $\pi(p^*;F)\ge\rho\,\pi(p;F)$, that is,
--   $$\frac{\pi(p^*;F)}{\max_p\pi(p;F)}\ge\rho .$$
--
--   Clauses 1–2 say that $p^*$ solves $\max_p\min_{F\in\mathscr F}\pi(p;F)$ with value $L$: it is the optimal robust price. Clause 3 is the distribution-free performance guarantee, which depends only on $\gamma$ and the coefficient of variation $\sigma/\mu$.
--
--   **Formalization Note** The paper proves the tightness of $L$ only at $p^*$ (Theorem 1(b)); clause 2 at every price is its claim that $p^*$ is optimal. At $\mu=c$ Lean's $L$ is $0$ (its factor $\mu-c$ vanishes), the true maximin value.
--
--   Differences from the source:
--
--   - reading: "nonnegative marginal costs" (p. 5), a standing assumption not repeated in the statement → hypothesis 0 ≤ c; reason: the paper's standing assumption, made explicit (trap 19)
--   - reading: μ > 0 is never written but is implied: γ = c/μ and δ = σ/μ are defined, and a law on [0, ∞) with σ > 0 has mean μ > 0 → hypothesis 0 < μ; reason: with c ≤ μ it excludes only μ = c = 0, where 𝓕 is empty and the statement is meaningless
--   - reading: "The optimal robust price is p∗", i.e. p∗ = arg max_p {min_{F∈𝓕} π(p;F)} (p. 9) → clauses (i) π(p*;F) ≥ L ∀ F ∈ 𝓕 and (ii) ∀ p, ∀ ε > 0, ∃ F ∈ 𝓕, π(p;F) < L + ε; reason: states maximin optimality with value L without real sup/inf (trap 5); the paper proves tightness only at p* (Theorem 1(b)), clause (ii) is its claim at every price
--   - encoding: π(p∗;F)/max_p π(p;F) ≥ ρ for all F ∈ 𝓕 → ∀ F ∈ 𝓕, ∀ p, ρ·π(p;F) ≤ π(p*;F); reason: equivalent: the maximum over p is attained and π(p*;F) ≥ L > 0 when c < μ; avoids division and a real supremum
--   - encoding: Assumption (P) μ ≥ c for the whole theorem → clauses (i)–(ii) under c ≤ μ; clause (iii) under c < μ; reason: at μ = c, τ = 0 and γ = 1 make ρ a 0/0 expression; this excludes only that undefined case
--   - encoding: k* = ∛(τ + √(τ²+1)) + ∛(τ − √(τ²+1)) → kStar τ = (√(τ²+1) + τ)^(1/3) − (√(τ²+1) − τ)^(1/3) with positive bases; reason: the real cube root is odd, so the two expressions are the same real number; Real.rpow of a negative base is not the real cube root
--   - encoding: 𝓕 = {F, v ≥ 0 | E[V] = μ, E[V²] = μ² + σ²} with "finite first and second moments" (p. 8) → valClass requires integrability of v and v² besides the two moment identities; reason: the paper's own finiteness of the moments; Lean's Bochner integral is 0 on non-integrable functions (trap 2)
-- source:
--   Chen, Hu, Perakis, Distribution-Free Pricing, accepted manuscript (MSOM, doi:10.1287/msom.2021.1055), Theorem 2, p. 11; proof OA p. 11

import Mathlib
import Definitions.Def_DistFreePricing_Maximin_Setting

namespace DistFreePricing.Maximin

open MeasureTheory

/-- Theorem 2 (robust price and performance guarantee, p. 11), for `0 ≤ c ≤ μ`, `μ > 0`, `σ > 0`:
`k* ≥ 0`; (i) `p* = μ − k*σ` earns at least `L` against every law in `𝓕`; (ii) no price does
better in the worst case: every real price `p` earns less than `L + ε` against some law in `𝓕`, so
`p*` is an optimal robust price with maximin value `L`; (iii) when `c < μ` (where `ρ` is defined),
`π(p*;F) ≥ ρ · π(p;F)` for every `F ∈ 𝓕` and every price `p`, i.e. `π(p*;F) / max_p π(p;F) ≥ ρ`. -/
theorem theorem_2 (c μ σ : ℝ) (hc : 0 ≤ c) (hcμ : c ≤ μ) (hμ : 0 < μ) (hσ : 0 < σ) :
    0 ≤ kStar (tau c μ σ) ∧
    (∀ F ∈ valClass μ σ, lowerL c μ σ ≤ profit c (pStar c μ σ) F) ∧
    (∀ p ε : ℝ, 0 < ε → ∃ F ∈ valClass μ σ, profit c p F < lowerL c μ σ + ε) ∧
    (c < μ → ∀ F ∈ valClass μ σ, ∀ p : ℝ,
      rho c μ σ * profit c p F ≤ profit c (pStar c μ σ) F) := by sorry

end DistFreePricing.Maximin
