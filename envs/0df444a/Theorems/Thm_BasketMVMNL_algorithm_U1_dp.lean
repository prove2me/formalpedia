-- Prove2me | Theorems.Thm_BasketMVMNL_algorithm_U1_dp
-- name    : BasketMVMNL.algorithm_U1_dp
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T10:31:38.341669+00:00
-- url     : https://prove2.me/theorems/4aae3ca4-73a9-4568-b2da-fb0ef5be12b3
-- title:
--   Algorithm U1, step 2 — the output maximizes $\bar R$ over revenue-ordered assortments
-- statement:
--   Under MVMNL with no interaction terms and the standing assumptions of §4, for every $\epsilon'>0$ the assortment $\bar x^*$ returned by Algorithm U1 is revenue-ordered in every group, and
--   $$
--   \bar R(\bar x^*)\ge\bar R(x)\quad\text{for every revenue-ordered assortment }x.
--   $$
--   For each $K\in\{J,\dots,JM\}$ the dynamic program attains $\bar V_1(1)=\bar R(x^K)=\max\{\bar R(x):x\text{ revenue-ordered},\ \bar\Gamma(x)=(1+\epsilon')^K\}$, and every revenue-ordered $x$ has $\bar\Gamma(x)=(1+\epsilon')^K$ for some such $K$; the output is the best candidate. This is the property the proof of (EC.6) uses ("since $\bar x^*=\arg\max_x\bar R(x)$ thus we have $\bar R(\bar x^*)\ge\bar R(x)$ for all $x$ that consist of revenue-ordered local assortments in each group").
--
--   Differences from the source:
--
--   - encoding: J groups of I products indexed (i,j) from 1; bundles y with yⱼ ∈ {0,1,…,I}; x ∈ {0,1}^{JI}; utilities θᵢ,ⱼ, μ₀ with vᵢ,ⱼ = exp θᵢ,ⱼ, v₀ = exp μ₀ → groups Fin J, products Fin I (0-based); bundles Fin J → Option (Fin I) with none for yⱼ = 0; x : Fin J → Fin I → Bool; the instance stores v, v₀ (θ = log v, μ₀ = log v₀), r and ψ; reason: the same instances, assortments and bundles
--   - encoding: "There are J groups of products and each group consists of I different products" (p.6) → 1 ≤ J and 1 ≤ I in Standing; reason: excludes only the empty instance, which the paper does not consider
--   - reading: rᵢ,ⱼ, "the revenue of product i in group j" (p.7), sign not stated → 0 ≤ rᵢ,ⱼ in Standing; reason: the plain meaning of revenue; with a negative revenue Theorem 1 is false (J = 2, I = 1, v = (0.2768, 10), r = (4.1257, −0.8847), v₀ = 53.3, ϵ = 0.1: Algorithm U1 earns 0.019083 < 0.9 · 0.021315)
--   - encoding: "Without loss of generality, we assume that the products in each group are ordered in such a way that the revenues {rᵢ,ⱼ} are non-increasing in i for each j" (p.9) → Standing.r_antitone: r j is antitone in i for every j; reason: the section's standing assumption; any instance is brought to this form by relabelling the products of each group, and revenue-ordered is defined with respect to this order
--   - reading: Algorithm U1 (p.13), described in prose and a box, with no cost model and no tie rule → the instrumented program algU1 in the unit-cost model Work: +, −, ×, /, comparisons, ⌈·⌉₊, array reads and writes and loop dispatch are charged where they execute; no log or exp; mⱼ is found by a multiplication loop; the DP state k stands for s = (1+ϵ′)^k; a K whose V̄₁(1) is −∞ gives no candidate; the first maximizer is kept (smallest t in a cell, smallest K overall); reason: the paper fixes neither a cost model nor a tie rule; any tie rule proves the theorem, and the operation count is the paper's count of DP evaluations
--   - encoding: (1+ϵ′)^{mⱼ−1} < γⱼ(xⱼ) ≤ (1+ϵ′)^{mⱼ}, mⱼ = 1 if xⱼ = 0; M = maxⱼ ⌈log_{1+ϵ′}(1 + Σᵢ vᵢ,ⱼ)⌉ → mexp ϵ′ γ = least m ≥ 1 with γ ≤ (1+ϵ′)^m; γ̄ = (1+ϵ′)^{mexp}; Mcap = maxⱼ mexp(1 + Σᵢ vᵢ,ⱼ); reason: the same integers for ϵ′ > 0, γ ≥ 1 and 1 + Σᵢ vᵢ,ⱼ > 1
--   - encoding: revenue-ordered: x∗ᵢ,ⱼ = 1 iff i ≤ i(j) → IsRO: for each j some t ≤ I with xⱼ i = true iff i < t (0-based); reason: the same prefixes; t = 0 is the empty local assortment
--   - reading: "(By definition, we have R̄(x^K) = V̄₁(1).)" and "Output: x̄∗ := argmax_{x∈{x^K : J≤K≤JM}} R̄(x)" → IsRO(x̄∗) and R̄(x) ≤ R̄(x̄∗) for every revenue-ordered x; reason: this is the content of the step as the proof of (EC.6) uses it (p.ec5)
-- source:
--   Jasin, Lyu, Najafi, Zhang, Assortment Optimization with Multi-Item Basket Purchase under Multivariate MNL Model, SSRN 3818886, Algorithm U1, p.13 (step 2, "By definition, we have R̄(x^K) = V̄₁(1)"; the enumeration K ∈ {J,…,JM}); EC.3, p.ec5

import Mathlib
import Definitions.Def_BasketMVMNL_Model
import Definitions.Def_BasketMVMNL_Rounding
import Definitions.Def_BasketMVMNL_Algorithm

namespace BasketMVMNL

/-- **Algorithm U1, step 2**, p.13: "(By definition, we have R̄(x^K) = V̄₁(1).)", with the
enumeration "We enumerate all possible values of Γ̄(x) = (1+ϵ′)^K, where K ∈ {J,J+1,...,JM}" and the
output `x̄* := argmax_{x∈{x^K : J≤K≤JM}} R̄(x)`. Jasin, Lyu, Najafi, Zhang, *Assortment Optimization with Multi-Item Basket Purchase under
Multivariate MNL Model*, SSRN 3818886.

For every `ϵ′ > 0`, the assortment `x̄*` returned by Algorithm U1 is revenue-ordered in every group
and maximizes the approximated revenue `R̄` over all revenue-ordered assortments:
`R̄(x̄*) ≥ R̄(x)` for every `x` that consists of revenue-ordered local assortments in each group
(EC.3, p.ec5). -/
theorem algorithm_U1_dp {J I : ℕ} (P : Instance J I) (hP : P.Standing) (hψ : NoInteraction P)
    (ε' : ℝ) (hε' : 0 < ε') :
    IsRO (output P ε') ∧ ∀ x : Assortment J I, IsRO x → Rbar ε' P x ≤ Rbar ε' P (output P ε') := by sorry

end BasketMVMNL
