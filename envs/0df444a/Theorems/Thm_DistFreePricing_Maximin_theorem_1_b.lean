-- Prove2me | Theorems.Thm_DistFreePricing_Maximin_theorem_1_b
-- name    : DistFreePricing.Maximin.theorem_1_b
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-23T03:55:45.664438+00:00
-- url     : https://prove2.me/theorems/21615e9e-9892-4081-8ab5-94279cfe9523
-- title:
--   Theorem 1(b), p. 10 — k* ≥ 0 and, for all F ∈ 𝓕, π(p*;F) ≥ L = (µ − c)(1 − 3k*/(2τ)), p* = µ − k*σ
-- statement:
--   **Distribution-free lower bound.** Let $0\le c\le\mu$ and $\sigma>0$, let $\tau=(\mu-c)/\sigma$, let $k^*=\sqrt[3]{\tau+\sqrt{\tau^2+1}}+\sqrt[3]{\tau-\sqrt{\tau^2+1}}$ and $p^*=\mu-k^*\sigma$. Then $k^*\ge0$, and for every valuation law $F\in\mathscr F$ (support in $[0,\infty)$, mean $\mu$, standard deviation $\sigma$),
--
--   $$\pi(p^*;F)=(p^*-c)\,\mathbb P_F(V\ge p^*)\;\ge\;L:=(\mu-c)\Big(1-\frac{3}{2\tau}k^*\Big).$$
--
--   Hence also $\max_p\pi(p;F)\ge L$. The price $p^*$ thus guarantees the profit $L$ whatever the valuation law with the given mean and variance.
--
--   Differences from the source:
--
--   - reading: "nonnegative marginal costs" (p. 5), a standing assumption not repeated in the statement → hypothesis 0 ≤ c; reason: the paper's standing assumption, made explicit (trap 19)
--   - encoding: max_p π(p;F) ≥ π(p∗;F) ≥ L → π(p*;F) ≥ L; reason: the first inequality holds by the definition of a maximum
--   - encoding: L = (μ − c)(1 − 3/(2τ) k∗), at μ = c with τ = 0 → Lean reads 3/(2·0) as 0, so L = 0 at μ = c; reason: the factor μ − c = 0 makes L = 0 under any reading, and 0 is the true worst-case profit there; no instance with μ > c changes
--   - encoding: k* = ∛(τ + √(τ²+1)) + ∛(τ − √(τ²+1)) → kStar τ = (√(τ²+1) + τ)^(1/3) − (√(τ²+1) − τ)^(1/3) with positive bases; reason: the real cube root is odd, so the two expressions are the same real number; Real.rpow of a negative base is not the real cube root
--   - encoding: 𝓕 = {F, v ≥ 0 | E[V] = μ, E[V²] = μ² + σ²} with "finite first and second moments" (p. 8) → valClass requires integrability of v and v² besides the two moment identities; reason: the paper's own finiteness of the moments; Lean's Bochner integral is 0 on non-integrable functions (trap 2)
-- source:
--   Chen, Hu, Perakis, Distribution-Free Pricing, accepted manuscript (MSOM, doi:10.1287/msom.2021.1055), Theorem 1(b), p. 10

import Mathlib
import Definitions.Def_DistFreePricing_Maximin_Setting

namespace DistFreePricing.Maximin

open MeasureTheory

/-- Theorem 1(b) (lower bound, p. 10): `k* ≥ 0`, and for every law `F ∈ 𝓕`,
`π(p*;F) ≥ L = (μ − c)(1 − 3k*/(2τ))`. -/
theorem theorem_1_b (c μ σ : ℝ) (hc : 0 ≤ c) (hcμ : c ≤ μ) (hσ : 0 < σ) :
    0 ≤ kStar (tau c μ σ) ∧
    ∀ F ∈ valClass μ σ, lowerL c μ σ ≤ profit c (pStar c μ σ) F := by sorry

end DistFreePricing.Maximin
