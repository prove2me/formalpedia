-- Prove2me | Theorems.Thm_BasketMVMNL_lemma_1
-- name    : BasketMVMNL.lemma_1
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T10:31:31.002707+00:00
-- url     : https://prove2.me/theorems/51e6989b-58dc-4f70-acb5-b65bc07be601
-- title:
--   Lemma 1 — the closed form of the purchase probability $P_{i,j}(x)$
-- statement:
--   Consider the MVMNL model with no interaction terms under the standing assumptions of §4. For every assortment $x$, every group $j$ and every product $i$, the probability that product $i$ of group $j$ is purchased is
--   $$
--   P_{i,j}(x)=\frac{v_{i,j}x_{i,j}\cdot\prod_{j'\neq j}\big(1+\sum_{i'}v_{i',j'}x_{i',j'}\big)}{v_0-1+\prod_{j'}\big(1+\sum_{i'}v_{i',j'}x_{i',j'}\big)}.
--   $$
--   Here $P_{i,j}(x)$ is the total probability, under the choice rule (3), of the permissible bundles that buy product $(i,j)$. The identity turns the sum over the $(I+1)^J$ bundles into a product over groups; (5) and (7) follow from it.
--
--   Differences from the source:
--
--   - encoding: J groups of I products indexed (i,j) from 1; bundles y with yⱼ ∈ {0,1,…,I}; x ∈ {0,1}^{JI}; utilities θᵢ,ⱼ, μ₀ with vᵢ,ⱼ = exp θᵢ,ⱼ, v₀ = exp μ₀ → groups Fin J, products Fin I (0-based); bundles Fin J → Option (Fin I) with none for yⱼ = 0; x : Fin J → Fin I → Bool; the instance stores v, v₀ (θ = log v, μ₀ = log v₀), r and ψ; reason: the same instances, assortments and bundles
--   - encoding: "There are J groups of products and each group consists of I different products" (p.6) → 1 ≤ J and 1 ≤ I in Standing; reason: excludes only the empty instance, which the paper does not consider
--   - reading: rᵢ,ⱼ, "the revenue of product i in group j" (p.7), sign not stated → 0 ≤ rᵢ,ⱼ in Standing; reason: the plain meaning of revenue; with a negative revenue Theorem 1 is false (J = 2, I = 1, v = (0.2768, 10), r = (4.1257, −0.8847), v₀ = 53.3, ϵ = 0.1: Algorithm U1 earns 0.019083 < 0.9 · 0.021315)
--   - encoding: "Without loss of generality, we assume that the products in each group are ordered in such a way that the revenues {rᵢ,ⱼ} are non-increasing in i for each j" (p.9) → Standing.r_antitone: r j is antitone in i for every j; reason: the section's standing assumption; any instance is brought to this form by relabelling the products of each group, and revenue-ordered is defined with respect to this order
--   - reading: (3)–(4) write exp{μ(y)} for every permissible y, while (1) gives y = 0 the utility μ₀ → μ(0) = μ₀ = log v₀, so the empty bundle has weight v₀; reason: the denominator v₀ + … of Lemma 1 fixes this meaning
--   - reading: the chain Pᵢ,ⱼ(x) = (expanded series) = (series over k) = closed form → Pᵢ,ⱼ(x) = closed form; reason: the middle expressions are expansions of the same quantity; the closed form is what (5) uses
--   - encoding: Pᵢ,ⱼ(x), "the probability that product i in group j is purchased under x" → Pij: the sum of the choice probabilities (3) of the permissible bundles with yⱼ = some i; reason: the same probability: the bundles are mutually exclusive outcomes
-- source:
--   Jasin, Lyu, Najafi, Zhang, Assortment Optimization with Multi-Item Basket Purchase under Multivariate MNL Model, SSRN 3818886, Lemma 1, pp.9–10

import Mathlib
import Definitions.Def_BasketMVMNL_Model
import Definitions.Def_BasketMVMNL_Rounding

namespace BasketMVMNL

/-- **Lemma 1**, pp.9–10. Jasin, Lyu, Najafi, Zhang, *Assortment Optimization with Multi-Item Basket Purchase under
Multivariate MNL Model*, SSRN 3818886.

Under MVMNL with no interaction terms, for every assortment `x`, group `j` and product `i`,
`Pᵢ,ⱼ(x) = vᵢ,ⱼ xᵢ,ⱼ · ∏_{j'≠j} (1 + Σ_{i'} v_{i',j'} x_{i',j'}) / (v₀ − 1 + ∏_{j'} (1 + Σ_{i'} v_{i',j'} x_{i',j'}))`,
where `Pᵢ,ⱼ(x)` is the total probability (3) of the permissible bundles that buy product `i` of
group `j`. -/
theorem lemma_1 {J I : ℕ} (P : Instance J I) (hP : P.Standing) (hψ : NoInteraction P)
    (x : Assortment J I) (j : Fin J) (i : Fin I) :
    Pij P x j i =
      P.v j i * bit (x j i) * (∏ j' ∈ Finset.univ.erase j, γ P x j') / (P.v0 - 1 + Γ P x) := by sorry

end BasketMVMNL
