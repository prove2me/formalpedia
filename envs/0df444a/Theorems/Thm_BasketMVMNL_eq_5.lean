-- Prove2me | Theorems.Thm_BasketMVMNL_eq_5
-- name    : BasketMVMNL.eq_5
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T10:31:36.31627+00:00
-- url     : https://prove2.me/theorems/651e2387-dad4-437f-85a6-c133ee6ffca9
-- title:
--   (5) — the closed form of the expected total revenue $R(x)$
-- statement:
--   Under MVMNL with no interaction terms and the standing assumptions of §4, the expected total revenue (4) of every assortment $x$ satisfies
--   $$
--   R(x)=\sum_{i,j}r_{i,j}P_{i,j}(x)=\frac{\sum_{i,j}r_{i,j}v_{i,j}x_{i,j}\cdot\prod_{j'\neq j}\big(1+\sum_{i'}v_{i',j'}x_{i',j'}\big)}{v_0-1+\prod_{j'}\big(1+\sum_{i'}v_{i',j'}x_{i',j'}\big)}.
--   $$
--   This closed form shows that the revenue is not decoupled across groups even without interaction terms, and it is the starting point of the analysis of (6).
--
--   Differences from the source:
--
--   - encoding: J groups of I products indexed (i,j) from 1; bundles y with yⱼ ∈ {0,1,…,I}; x ∈ {0,1}^{JI}; utilities θᵢ,ⱼ, μ₀ with vᵢ,ⱼ = exp θᵢ,ⱼ, v₀ = exp μ₀ → groups Fin J, products Fin I (0-based); bundles Fin J → Option (Fin I) with none for yⱼ = 0; x : Fin J → Fin I → Bool; the instance stores v, v₀ (θ = log v, μ₀ = log v₀), r and ψ; reason: the same instances, assortments and bundles
--   - encoding: "There are J groups of products and each group consists of I different products" (p.6) → 1 ≤ J and 1 ≤ I in Standing; reason: excludes only the empty instance, which the paper does not consider
--   - reading: rᵢ,ⱼ, "the revenue of product i in group j" (p.7), sign not stated → 0 ≤ rᵢ,ⱼ in Standing; reason: the plain meaning of revenue; with a negative revenue Theorem 1 is false (J = 2, I = 1, v = (0.2768, 10), r = (4.1257, −0.8847), v₀ = 53.3, ϵ = 0.1: Algorithm U1 earns 0.019083 < 0.9 · 0.021315)
--   - encoding: "Without loss of generality, we assume that the products in each group are ordered in such a way that the revenues {rᵢ,ⱼ} are non-increasing in i for each j" (p.9) → Standing.r_antitone: r j is antitone in i for every j; reason: the section's standing assumption; any instance is brought to this form by relabelling the products of each group, and revenue-ordered is defined with respect to this order
--   - reading: (3)–(4) write exp{μ(y)} for every permissible y, while (1) gives y = 0 the utility μ₀ → μ(0) = μ₀ = log v₀, so the empty bundle has weight v₀; reason: the denominator v₀ + … of Lemma 1 fixes this meaning
-- source:
--   Jasin, Lyu, Najafi, Zhang, Assortment Optimization with Multi-Item Basket Purchase under Multivariate MNL Model, SSRN 3818886, (5), p.10

import Mathlib
import Definitions.Def_BasketMVMNL_Model
import Definitions.Def_BasketMVMNL_Rounding

namespace BasketMVMNL

/-- **Equation (5)**, p.10. Jasin, Lyu, Najafi, Zhang, *Assortment Optimization with Multi-Item Basket Purchase under
Multivariate MNL Model*, SSRN 3818886.

Under MVMNL with no interaction terms, the expected total revenue (4) satisfies
`R(x) = Σ_{i,j} rᵢ,ⱼ Pᵢ,ⱼ(x) = Σ_{i,j} rᵢ,ⱼ vᵢ,ⱼ xᵢ,ⱼ · ∏_{j'≠j} γ_{j'}(x_{j'}) / (v₀ − 1 + ∏_{j'} γ_{j'}(x_{j'}))`
for every assortment `x`, with `γⱼ(xⱼ) = 1 + Σᵢ vᵢ,ⱼ xᵢ,ⱼ`. -/
theorem eq_5 {J I : ℕ} (P : Instance J I) (hP : P.Standing) (hψ : NoInteraction P)
    (x : Assortment J I) :
    R P x = ∑ j, ∑ i, P.r j i * Pij P x j i ∧
    R P x = (∑ j, ∑ i, P.r j i * P.v j i * bit (x j i) * ∏ j' ∈ Finset.univ.erase j, γ P x j') /
      (P.v0 - 1 + Γ P x) := by sorry

end BasketMVMNL
