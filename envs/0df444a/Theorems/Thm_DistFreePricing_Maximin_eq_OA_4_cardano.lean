-- Prove2me | Theorems.Thm_DistFreePricing_Maximin_eq_OA_4_cardano
-- name    : DistFreePricing.Maximin.eq_OA_4_cardano
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-23T03:55:32.349351+00:00
-- url     : https://prove2.me/theorems/abdafdf3-7687-4b5c-9277-9f7fe4ba9435
-- title:
--   (OA.4) and Cardano, OA p. 11 — φ′(k) = 0 ⇔ k³ + 3k = 2τ for k ≠ 0; φ minimal at 0 and τ on [0, τ]; k* is the unique real root, k* ≥ 0
-- statement:
--   **The stationarity cubic and its Cardano root.** For $\tau\ge0$ let $\varphi(k)=(1-k/\tau)\big(1-\frac1{1+k^2}\big)$ (defined for $\tau>0$) and
--   $$k^*(\tau)=\sqrt[3]{\tau+\sqrt{\tau^2+1}}+\sqrt[3]{\tau-\sqrt{\tau^2+1}}.$$
--   Then:
--
--   1. if $\tau>0$, a point $k\ne0$ is a stationary point of $\varphi$ exactly when it solves the cubic (OA.4):
--   $$\varphi'(k)=0\iff k^3+3k=2\tau ;$$
--   2. if $\tau>0$, $\varphi$ is minimized over $[0,\tau]$ at $k=0$ and at $k=\tau$: $\varphi(0)\le\varphi(k)$ and $\varphi(\tau)\le\varphi(k)$ for $0\le k\le\tau$;
--   3. $k^*$ solves the cubic: $(k^*)^3+3k^*=2\tau$;
--   4. $k^*$ is its only real root: every $k\in\mathbb R$ with $k^3+3k=2\tau$ equals $k^*$;
--   5. $k^*\ge0$.
--
--   The safety factor $k^*$ of the robust price $p^*=\mu-k^*\sigma$ is thereby identified as the unique interior critical point of the lower-bound function $\varphi$.
--
--   **Formalization Note** The derivative is Lean's `deriv` of $k\mapsto\varphi(k)$ for the fixed $\tau$.
--
--   Differences from the source:
--
--   - encoding: τ ≥ 0 (Assumption (P)); φ(k) = (1 − kσ/(μ − c))(1 − 1/(1+k²)) → the stationarity and minimization clauses assume 0 < t; φ is written with k/τ; reason: φ divides by μ − c, i.e. by τ, so it is undefined at τ = 0; kσ/(μ − c) = k/τ
--   - reading: "(The function ϕ(k) is minimized at k = 0 or k = (µ−c)/σ.)" → for 0 ≤ k ≤ τ: φ(0) ≤ φ(k) and φ(τ) ≤ φ(k); reason: minimized over [0, τ], the range of k in (OA.3); on ℝ φ is unbounded below (φ(k) → −∞ as k → +∞)
--   - encoding: k* = ∛(τ + √(τ²+1)) + ∛(τ − √(τ²+1)) → kStar τ = (√(τ²+1) + τ)^(1/3) − (√(τ²+1) − τ)^(1/3) with positive bases; reason: the real cube root is odd, so the two expressions are the same real number; Real.rpow of a negative base is not the real cube root
-- source:
--   Chen, Hu, Perakis, Distribution-Free Pricing, accepted manuscript (MSOM, doi:10.1287/msom.2021.1055), (OA.4) and the Cardano sentence, proof of Theorem 1(b), OA p. 11

import Mathlib
import Definitions.Def_DistFreePricing_Maximin_Setting

namespace DistFreePricing.Maximin

open MeasureTheory

/-- (OA.4) and Cardano's root (proof of Theorem 1(b), OA p. 11), for `τ ≥ 0`: when `τ > 0` the
non-zero stationary points of `φ` are the real roots of `k³ + 3k = 2τ`, and `φ` is minimized over
`[0, τ]` at `k = 0` and at `k = τ`; `k*(τ)` is the unique real root of the cubic, and `k* ≥ 0`. -/
theorem eq_OA_4_cardano (t : ℝ) (ht : 0 ≤ t) :
    (0 < t → ∀ k : ℝ, k ≠ 0 → (deriv (phi t) k = 0 ↔ k ^ 3 + 3 * k = 2 * t)) ∧
    (0 < t → ∀ k : ℝ, 0 ≤ k → k ≤ t → phi t 0 ≤ phi t k ∧ phi t t ≤ phi t k) ∧
    kStar t ^ 3 + 3 * kStar t = 2 * t ∧
    (∀ k : ℝ, k ^ 3 + 3 * k = 2 * t → k = kStar t) ∧
    0 ≤ kStar t := by sorry

end DistFreePricing.Maximin
