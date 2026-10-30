-- Prove2me | Theorems.Thm_DistFreePricing_Maximin_eq_OA_5
-- name    : DistFreePricing.Maximin.eq_OA_5
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-23T03:55:31.063178+00:00
-- url     : https://prove2.me/theorems/845e1c85-6676-404f-b1c8-7c2c8c0b303a
-- title:
--   (OA.5), OA p. 11 — φ is maximized on [0, τ] at k*, and φ(k*) = (k*)²/((k*)²+3) = (k*)³/(2τ) = 1 − 3k*/(2τ)
-- statement:
--   **Maximum of the lower-bound function.** Let $\tau>0$, $\varphi(k)=(1-k/\tau)\big(1-\frac1{1+k^2}\big)$ and $k^*=k^*(\tau)$ Cardano's root of $k^3+3k=2\tau$. Then $\varphi(k)\le\varphi(k^*)$ for every $k\in[0,\tau]$, and
--
--   $$\varphi(k^*)=\Big(1-\frac{k^*}{\tau}\Big)\Big(1-\frac{1}{1+(k^*)^2}\Big)=\frac{(k^*)^2}{(k^*)^2+3}=\frac{(k^*)^3}{2\tau}=1-\frac{3}{2\tau}k^* .$$
--
--   Combined with (OA.3), this gives the distribution-free lower bound $L=(\mu-c)\varphi(k^*)$ of Theorem 1(b).
--
--   Differences from the source:
--
--   - encoding: τ ≥ 0 (Assumption (P)) → hypothesis 0 < t; reason: φ and 3/(2τ) divide by τ and are undefined at τ = 0
--   - reading: "ϕ(k) is maximized at k = k∗" → φ(k) ≤ φ(k*) for every k ∈ [0, τ]; reason: [0, τ] is the range of k in (OA.3) (k ≥ 0, p ≥ c); on ℝ the claim is false since φ(k) → +∞ as k → −∞
--   - encoding: k* = ∛(τ + √(τ²+1)) + ∛(τ − √(τ²+1)) → kStar τ = (√(τ²+1) + τ)^(1/3) − (√(τ²+1) − τ)^(1/3) with positive bases; reason: the real cube root is odd, so the two expressions are the same real number; Real.rpow of a negative base is not the real cube root
-- source:
--   Chen, Hu, Perakis, Distribution-Free Pricing, accepted manuscript (MSOM, doi:10.1287/msom.2021.1055), (OA.5), proof of Theorem 1(b), OA p. 11

import Mathlib
import Definitions.Def_DistFreePricing_Maximin_Setting

namespace DistFreePricing.Maximin

open MeasureTheory

/-- (OA.5) (proof of Theorem 1(b), OA p. 11): for `τ > 0`, `φ` is maximized over `[0, τ]` at `k*`, and
`φ(k*) = (k*)²/((k*)² + 3) = (k*)³/(2τ) = 1 − 3k*/(2τ)`. -/
theorem eq_OA_5 (t : ℝ) (ht : 0 < t) :
    (∀ k : ℝ, 0 ≤ k → k ≤ t → phi t k ≤ phi t (kStar t)) ∧
    phi t (kStar t) = kStar t ^ 2 / (kStar t ^ 2 + 3) ∧
    phi t (kStar t) = kStar t ^ 3 / (2 * t) ∧
    phi t (kStar t) = 1 - 3 / (2 * t) * kStar t := by sorry

end DistFreePricing.Maximin
