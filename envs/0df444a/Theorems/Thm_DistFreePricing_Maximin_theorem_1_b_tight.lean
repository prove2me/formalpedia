-- Prove2me | Theorems.Thm_DistFreePricing_Maximin_theorem_1_b_tight
-- name    : DistFreePricing.Maximin.theorem_1_b_tight
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-23T03:55:34.485616+00:00
-- url     : https://prove2.me/theorems/06d323db-7738-4686-a1a0-9813299bb2d9
-- title:
--   Theorem 1(b), p. 10 — L is asymptotically attained at p* by the two-point laws with k_ϵ = k* + ϵ, ϵ ↘ 0
-- statement:
--   **Tightness of the lower bound.** Let $0\le c\le\mu$, $\mu>0$, $\sigma>0$, and let $\tau$, $k^*$, $p^*=\mu-k^*\sigma$ and $L=(\mu-c)(1-\frac{3}{2\tau}k^*)$ be as in Theorem 1(b). For $\epsilon>0$ let $k_\epsilon=k^*+\epsilon$ and let $F_\epsilon$ be the two-point law
--
--   $$V=\begin{cases}\mu-k_\epsilon\sigma&\text{with probability }\frac{1}{1+k_\epsilon^2},\\[2pt] \mu+\frac{1}{k_\epsilon}\sigma&\text{with probability }1-\frac{1}{1+k_\epsilon^2}.\end{cases}$$
--
--   Then $F_\epsilon\in\mathscr F$ for all sufficiently small $\epsilon>0$, and
--
--   $$\lim_{\epsilon\searrow0}\pi(p^*;F_\epsilon)=L .$$
--
--   So no better guarantee than $L$ is possible at the price $p^*$: the worst-case profit of $p^*$ over $\mathscr F$ is exactly $L$.
--
--   Differences from the source:
--
--   - reading: "nonnegative marginal costs" (p. 5), a standing assumption not repeated in the statement → hypothesis 0 ≤ c; reason: the paper's standing assumption, made explicit (trap 19)
--   - reading: μ > 0 is never written but is implied: γ = c/μ and δ = σ/μ are defined, and a law on [0, ∞) with σ > 0 has mean μ > 0 → hypothesis 0 < μ; reason: with c ≤ μ it excludes only μ = c = 0, where 𝓕 is empty and the statement is meaningless
--   - reading: "a series of two-point distributions … with k_ϵ = k∗ + ϵ, as ϵ ↘ 0" (the proof adds "for any ϵ") → the two-point law lies in 𝓕 for all sufficiently small ε > 0 (∀ᶠ ε in 𝓝[>] 0); reason: for large ε the low atom μ − k_εσ is negative and the law leaves 𝓕 (μ = σ = 1, c = 0, ε = 10); the statement is about ε ↘ 0
--   - encoding: "the lower bound is asymptotically achievable" → π(p*; F_ε) → L as ε → 0⁺ (Tendsto … 𝓝[>] 0 (𝓝 L)); reason: the proof's own meaning: the profit "is asymptotically approximated to the lower bound … as ϵ ↘ 0"
--   - encoding: k* = ∛(τ + √(τ²+1)) + ∛(τ − √(τ²+1)) → kStar τ = (√(τ²+1) + τ)^(1/3) − (√(τ²+1) − τ)^(1/3) with positive bases; reason: the real cube root is odd, so the two expressions are the same real number; Real.rpow of a negative base is not the real cube root
--   - encoding: 𝓕 = {F, v ≥ 0 | E[V] = μ, E[V²] = μ² + σ²} with "finite first and second moments" (p. 8) → valClass requires integrability of v and v² besides the two moment identities; reason: the paper's own finiteness of the moments; Lean's Bochner integral is 0 on non-integrable functions (trap 2)
-- source:
--   Chen, Hu, Perakis, Distribution-Free Pricing, accepted manuscript (MSOM, doi:10.1287/msom.2021.1055), Theorem 1(b), p. 10; proof OA p. 11

import Mathlib
import Definitions.Def_DistFreePricing_Maximin_Setting

namespace DistFreePricing.Maximin

open MeasureTheory

open Filter Topology

/-- Theorem 1(b), tightness (p. 10; proof OA p. 11): for all sufficiently small `ε > 0` the two-point
law with `k_ε = k* + ε` lies in `𝓕`, and its profit at `p*` tends to `L` as `ε ↘ 0`. -/
theorem theorem_1_b_tight (c μ σ : ℝ) (hc : 0 ≤ c) (hcμ : c ≤ μ) (hμ : 0 < μ) (hσ : 0 < σ) :
    (∀ᶠ ε in 𝓝[>] (0 : ℝ), twoPoint μ σ (kStar (tau c μ σ) + ε) ∈ valClass μ σ) ∧
    Tendsto (fun ε : ℝ => profit c (pStar c μ σ) (twoPoint μ σ (kStar (tau c μ σ) + ε)))
      (𝓝[>] 0) (𝓝 (lowerL c μ σ)) := by sorry

end DistFreePricing.Maximin
