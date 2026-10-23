-- Prove2me | Theorems.Thm_DistFreePricing_Maximin_theorem_1_a
-- name    : DistFreePricing.Maximin.theorem_1_a
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-23T03:55:36.195194+00:00
-- url     : https://prove2.me/theorems/c3d5a83f-d575-42ce-929c-2a55b65a3904
-- title:
--   Theorem 1(a), p. 10 — for all F ∈ 𝓕 and all prices p, π(p;F) ≤ U = µ − τ²/(1+τ²)·c
-- statement:
--   **Distribution-free upper bound.** Let $0\le c\le\mu$ and $\sigma>0$, and let $\mathscr F$ be the class of valuation laws on $[0,\infty)$ with mean $\mu$ and standard deviation $\sigma$. With $\tau=(\mu-c)/\sigma$ and $\pi(p;F)=(p-c)\,\mathbb P_F(V\ge p)$, for every $F\in\mathscr F$ and every price $p\in\mathbb R$,
--
--   $$\pi(p;F)\le U:=\mu-\frac{\tau^2}{1+\tau^2}\,c .$$
--
--   Equivalently, $\max_p\pi(p;F)\le U$ for all $F\in\mathscr F$. The bound exceeds $\mu-c$, the profit of perfect price discrimination with every customer paying $V$ when $V\ge c$; it is the denominator of the performance guarantee of Theorem 2.
--
--   Differences from the source:
--
--   - reading: "nonnegative marginal costs" (p. 5), a standing assumption not repeated in the statement → hypothesis 0 ≤ c; reason: the paper's standing assumption, made explicit (trap 19)
--   - encoding: max_p π(p;F) ≤ U → ∀ p, π(p;F) ≤ U; reason: equivalent to the printed bound (the maximum is attained); avoids a real supremum (trap 5)
--   - encoding: 𝓕 = {F, v ≥ 0 | E[V] = μ, E[V²] = μ² + σ²} with "finite first and second moments" (p. 8) → valClass requires integrability of v and v² besides the two moment identities; reason: the paper's own finiteness of the moments; Lean's Bochner integral is 0 on non-integrable functions (trap 2)
-- source:
--   Chen, Hu, Perakis, Distribution-Free Pricing, accepted manuscript (MSOM, doi:10.1287/msom.2021.1055), Theorem 1(a), p. 10; proof OA pp. 10–11, (OA.1)–(OA.2)

import Mathlib
import Definitions.Def_DistFreePricing_Maximin_Setting

namespace DistFreePricing.Maximin

open MeasureTheory

/-- Theorem 1(a) (upper bound, p. 10): for every law `F ∈ 𝓕` and every price `p`,
`π(p;F) ≤ U = μ − τ²/(1 + τ²) · c`. -/
theorem theorem_1_a (c μ σ : ℝ) (hc : 0 ≤ c) (hcμ : c ≤ μ) (hσ : 0 < σ) :
    ∀ F ∈ valClass μ σ, ∀ p : ℝ, profit c p F ≤ upperU c μ σ := by sorry

end DistFreePricing.Maximin
