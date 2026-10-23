-- Prove2me | Theorems.Thm_DistFreePricing_Maximin_kStar_le
-- name    : DistFreePricing.Maximin.kStar_le
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-23T03:55:34.104688+00:00
-- url     : https://prove2.me/theorems/902a2532-413d-411e-b902-139902b08c51
-- title:
--   Proof of Theorem 1(b), OA p. 11 — k* ≤ 2τ/3 ≤ τ, hence p* = µ − k*σ ≥ c
-- statement:
--   **The robust price covers the cost.** Let $0\le c\le\mu$, $\sigma>0$ and $\tau=(\mu-c)/\sigma$. Then
--
--   $$k^*(\tau)\le\frac{2\tau}{3}\le\tau,\qquad\text{hence}\qquad p^*=\mu-k^*\sigma\ge c .$$
--
--   So the safety factor stays in the range $[0,\tau]$ where the lower bound (OA.3) applies, and the robust price is never below marginal cost.
--
--   Differences from the source:
--
--   - reading: "nonnegative marginal costs" (p. 5), a standing assumption not repeated in the statement → hypothesis 0 ≤ c; reason: the paper's standing assumption, made explicit (trap 19)
--   - encoding: k* = ∛(τ + √(τ²+1)) + ∛(τ − √(τ²+1)) → kStar τ = (√(τ²+1) + τ)^(1/3) − (√(τ²+1) − τ)^(1/3) with positive bases; reason: the real cube root is odd, so the two expressions are the same real number; Real.rpow of a negative base is not the real cube root
-- source:
--   Chen, Hu, Perakis, Distribution-Free Pricing, accepted manuscript (MSOM, doi:10.1287/msom.2021.1055), proof of Theorem 1(b), OA p. 11

import Mathlib
import Definitions.Def_DistFreePricing_Maximin_Setting

namespace DistFreePricing.Maximin

open MeasureTheory

/-- Proof of Theorem 1(b), OA p. 11: `k* ≤ 2τ/3 ≤ τ = (μ − c)/σ`, hence `p* = μ − k*σ ≥ c`. -/
theorem kStar_le (c μ σ : ℝ) (hc : 0 ≤ c) (hcμ : c ≤ μ) (hσ : 0 < σ) :
    kStar (tau c μ σ) ≤ 2 * tau c μ σ / 3 ∧ 2 * tau c μ σ / 3 ≤ tau c μ σ ∧
      c ≤ pStar c μ σ := by sorry

end DistFreePricing.Maximin
