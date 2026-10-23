-- Prove2me | Theorems.Thm_DistFreePricing_Maximin_eq_OA_3
-- name    : DistFreePricing.Maximin.eq_OA_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-23T03:55:28.854003+00:00
-- url     : https://prove2.me/theorems/bf186dec-2908-4e63-8ba7-0548d5e99be5
-- title:
--   (OA.3), OA p. 11 — for 0 ≤ k ≤ τ and F ∈ 𝓕, π(µ − kσ;F) ≥ (µ − kσ − c)(1 − 1/(1+k²))
-- statement:
--   **Lower bound at a safety-factor price.** Let $0\le c\le\mu$, $\sigma>0$, $\tau=(\mu-c)/\sigma$, and consider a price of the form $p=\mu-k\sigma$ with $0\le k\le\tau$ (equivalently $p\ge c$ and $k\ge 0$). For every valuation law $F\in\mathscr F$,
--
--   $$\pi(\mu-k\sigma;F)\;\ge\;(\mu-k\sigma-c)\Big(1-\frac{1}{1+k^2}\Big)\;=\;(\mu-c)\,\varphi(k),$$
--
--   where $\varphi(k)=\big(1-\frac{k\sigma}{\mu-c}\big)\big(1-\frac{1}{1+k^2}\big)$.
--
--   This turns the pricing problem against the worst law into maximizing the explicit function $\varphi$ over $k\in[0,\tau]$, which is how the robust price $p^*$ is found.
--
--   Differences from the source:
--
--   - reading: "nonnegative marginal costs" (p. 5), a standing assumption not repeated in the statement → hypothesis 0 ≤ c; reason: the paper's standing assumption, made explicit (trap 19)
--   - encoding: the chain max_{p>c} π(p;F) ≥ π(μ − kσ;F) = (μ − kσ − c)P(V ≥ μ − kσ) ≥ … → only π(μ − kσ;F) ≥ … is stated; reason: the first inequality holds by the definition of a maximum and the equality is the definition of π (`profit`)
--   - encoding: right-hand side (μ − c)(1 − kσ/(μ − c))(1 − 1/(1 + k²)) → (μ − kσ − c)(1 − 1/(1 + k²)); reason: equal for μ > c; at μ = c the printed form divides by 0, and 0 ≤ k ≤ τ = 0 forces k = 0, where both sides are 0
--   - encoding: 𝓕 = {F, v ≥ 0 | E[V] = μ, E[V²] = μ² + σ²} with "finite first and second moments" (p. 8) → valClass requires integrability of v and v² besides the two moment identities; reason: the paper's own finiteness of the moments; Lean's Bochner integral is 0 on non-integrable functions (trap 2)
-- source:
--   Chen, Hu, Perakis, Distribution-Free Pricing, accepted manuscript (MSOM, doi:10.1287/msom.2021.1055), (OA.3), proof of Theorem 1(b), OA p. 11

import Mathlib
import Definitions.Def_DistFreePricing_Maximin_Setting

namespace DistFreePricing.Maximin

open MeasureTheory

/-- (OA.3) (proof of Theorem 1(b), OA p. 11): for a price `p = μ − kσ` with `0 ≤ k ≤ τ` and every
`F ∈ 𝓕`, `π(μ − kσ;F) ≥ (μ − kσ − c)(1 − 1/(1 + k²))`. -/
theorem eq_OA_3 (c μ σ : ℝ) (hc : 0 ≤ c) (hcμ : c ≤ μ) (hσ : 0 < σ) (k : ℝ) (hk0 : 0 ≤ k)
    (hkτ : k ≤ tau c μ σ) :
    ∀ F ∈ valClass μ σ, (μ - k * σ - c) * (1 - 1 / (1 + k ^ 2)) ≤ profit c (μ - k * σ) F := by sorry

end DistFreePricing.Maximin
