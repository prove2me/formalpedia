-- Prove2me | Theorems.Thm_BasketMVMNL_M_bound
-- name    : BasketMVMNL.M_bound
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T10:31:45.517786+00:00
-- url     : https://prove2.me/theorems/44527c94-bdc8-48b9-afde-d014088cb0ec
-- title:
--   EC.3 — the bound on $M$ (corrected: $M\le1+4J\log\beta/\epsilon$ for $O(2J\epsilon^{-1}\log\beta)$)
-- statement:
--   Under the standing assumptions of §4 (no interaction terms), for every $\epsilon\in(0,1)$ and $\epsilon'=\epsilon/(2J)$,
--   $$
--   M=\max_j\Big\lceil\log_{1+\epsilon'}\Big(1+\sum_i v_{i,j}\Big)\Big\rceil\le1+\frac{4J\log\beta}{\epsilon},\qquad\beta=\max_j\Big(1+\sum_i v_{i,j}\Big).
--   $$
--   Combined with the $O(J^3M^2I)$ count, it gives the polynomial running time of Theorem 1.
--
--   Differences from the source:
--
--   - encoding: J groups of I products indexed (i,j) from 1; bundles y with yⱼ ∈ {0,1,…,I}; x ∈ {0,1}^{JI}; utilities θᵢ,ⱼ, μ₀ with vᵢ,ⱼ = exp θᵢ,ⱼ, v₀ = exp μ₀ → groups Fin J, products Fin I (0-based); bundles Fin J → Option (Fin I) with none for yⱼ = 0; x : Fin J → Fin I → Bool; the instance stores v, v₀ (θ = log v, μ₀ = log v₀), r and ψ; reason: the same instances, assortments and bundles
--   - encoding: "There are J groups of products and each group consists of I different products" (p.6) → 1 ≤ J and 1 ≤ I in Standing; reason: excludes only the empty instance, which the paper does not consider
--   - reading: rᵢ,ⱼ, "the revenue of product i in group j" (p.7), sign not stated → 0 ≤ rᵢ,ⱼ in Standing; reason: the plain meaning of revenue; with a negative revenue Theorem 1 is false (J = 2, I = 1, v = (0.2768, 10), r = (4.1257, −0.8847), v₀ = 53.3, ϵ = 0.1: Algorithm U1 earns 0.019083 < 0.9 · 0.021315)
--   - encoding: "Without loss of generality, we assume that the products in each group are ordered in such a way that the revenues {rᵢ,ⱼ} are non-increasing in i for each j" (p.9) → Standing.r_antitone: r j is antitone in i for every j; reason: the section's standing assumption; any instance is brought to this form by relabelling the products of each group, and revenue-ordered is defined with respect to this order
--   - encoding: (1+ϵ′)^{mⱼ−1} < γⱼ(xⱼ) ≤ (1+ϵ′)^{mⱼ}, mⱼ = 1 if xⱼ = 0; M = maxⱼ ⌈log_{1+ϵ′}(1 + Σᵢ vᵢ,ⱼ)⌉ → mexp ϵ′ γ = least m ≥ 1 with γ ≤ (1+ϵ′)^m; γ̄ = (1+ϵ′)^{mexp}; Mcap = maxⱼ mexp(1 + Σᵢ vᵢ,ⱼ); reason: the same integers for ϵ′ > 0, γ ≥ 1 and 1 + Σᵢ vᵢ,ⱼ > 1
--   - correction: M = O(2Jϵ⁻¹ log β) → M ≤ 1 + 4J log β/ϵ; reason: as a bound with a universal constant the printed one is false when β is close to 1: J = I = 1, v₁,₁ = δ, v₀ = 2, r₁,₁ = 1, ϵ = 1/2 gives M = 1 for δ ≤ ϵ′ while C·2Jϵ⁻¹ log(1+δ) → 0 as δ → 0; the additive 1 is the minimal correction, and 4 = 2 · 2 makes the constant explicit (log(1+ϵ′) ≥ ϵ′/2 for ϵ′ ≤ 1)
-- source:
--   Jasin, Lyu, Najafi, Zhang, Assortment Optimization with Multi-Item Basket Purchase under Multivariate MNL Model, SSRN 3818886, EC.3, p.ec6, "M = O(log_{1+ϵ′} β) = O(2Jϵ⁻¹ log β)"

import Mathlib
import Definitions.Def_BasketMVMNL_Model
import Definitions.Def_BasketMVMNL_Rounding

namespace BasketMVMNL

/-- **EC.3, p.ec6, the bound on `M`** (corrected): the paper writes
"M = O(log_{1+ϵ′} β) = O(2Jϵ⁻¹ log β), where β := maxⱼ(1 + Σᵢ vᵢ,ⱼ)". Jasin, Lyu, Najafi, Zhang, *Assortment Optimization with Multi-Item Basket Purchase under
Multivariate MNL Model*, SSRN 3818886.

For every `ϵ ∈ (0,1)`, with `ϵ′ = ϵ/(2J)`, `M ≤ 1 + 4J log β/ϵ`.

**Formalization Note.** The printed bound `O(2Jϵ⁻¹ log β)` has no additive term and fails as
`β → 1`, where `M ≥ 1` while `2Jϵ⁻¹ log β → 0`; the `1 +` is the minimal correction. -/
theorem M_bound {J I : ℕ} (P : Instance J I) (hP : P.Standing) (hψ : NoInteraction P)
    (ε : ℝ) (hε : 0 < ε) (hε1 : ε < 1) :
    (Mcap (ε / (2 * (J : ℝ))) P : ℝ) ≤ 1 + 4 * (J : ℝ) * Real.log (β P) / ε := by sorry

end BasketMVMNL
