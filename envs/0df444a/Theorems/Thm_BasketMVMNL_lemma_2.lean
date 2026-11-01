-- Prove2me | Theorems.Thm_BasketMVMNL_lemma_2
-- name    : BasketMVMNL.lemma_2
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T10:31:46.460375+00:00
-- url     : https://prove2.me/theorems/10a81f9d-efe5-4841-9b8a-efb1c7846c2c
-- title:
--   Lemma 2 — a revenue-ordered optimal assortment exists
-- statement:
--   Under MVMNL with no interaction terms and the standing assumptions of §4 there is an optimal assortment $x^*$ of
--   $$
--   \max_{x\in\{0,1\}^{JI}}R(x)\tag{6}
--   $$
--   that consists of revenue-ordered local assortments in each group: for each $j$ there is $i(j)$ such that $x^*_{i,j}=1$ iff $i\le i(j)$.
--
--   The thresholds of different groups cannot be computed separately, but the lemma restricts the search to $(I+1)^J$ candidates, and it is what lets Algorithm U1 range over revenue-ordered local assortments only.
--
--   Differences from the source:
--
--   - encoding: J groups of I products indexed (i,j) from 1; bundles y with yⱼ ∈ {0,1,…,I}; x ∈ {0,1}^{JI}; utilities θᵢ,ⱼ, μ₀ with vᵢ,ⱼ = exp θᵢ,ⱼ, v₀ = exp μ₀ → groups Fin J, products Fin I (0-based); bundles Fin J → Option (Fin I) with none for yⱼ = 0; x : Fin J → Fin I → Bool; the instance stores v, v₀ (θ = log v, μ₀ = log v₀), r and ψ; reason: the same instances, assortments and bundles
--   - encoding: "There are J groups of products and each group consists of I different products" (p.6) → 1 ≤ J and 1 ≤ I in Standing; reason: excludes only the empty instance, which the paper does not consider
--   - reading: rᵢ,ⱼ, "the revenue of product i in group j" (p.7), sign not stated → 0 ≤ rᵢ,ⱼ in Standing; reason: the plain meaning of revenue; with a negative revenue Theorem 1 is false (J = 2, I = 1, v = (0.2768, 10), r = (4.1257, −0.8847), v₀ = 53.3, ϵ = 0.1: Algorithm U1 earns 0.019083 < 0.9 · 0.021315)
--   - encoding: "Without loss of generality, we assume that the products in each group are ordered in such a way that the revenues {rᵢ,ⱼ} are non-increasing in i for each j" (p.9) → Standing.r_antitone: r j is antitone in i for every j; reason: the section's standing assumption; any instance is brought to this form by relabelling the products of each group, and revenue-ordered is defined with respect to this order
--   - reading: (3)–(4) write exp{μ(y)} for every permissible y, while (1) gives y = 0 the utility μ₀ → μ(0) = μ₀ = log v₀, so the empty bundle has weight v₀; reason: the denominator v₀ + … of Lemma 1 fixes this meaning
--   - encoding: revenue-ordered: x∗ᵢ,ⱼ = 1 iff i ≤ i(j) → IsRO: for each j some t ≤ I with xⱼ i = true iff i < t (0-based); reason: the same prefixes; t = 0 is the empty local assortment
-- source:
--   Jasin, Lyu, Najafi, Zhang, Assortment Optimization with Multi-Item Basket Purchase under Multivariate MNL Model, SSRN 3818886, Lemma 2, p.10 (proof EC.1, p.ec2)

import Mathlib
import Definitions.Def_BasketMVMNL_Model
import Definitions.Def_BasketMVMNL_Rounding

namespace BasketMVMNL

/-- **Lemma 2**, p.10. Jasin, Lyu, Najafi, Zhang, *Assortment Optimization with Multi-Item Basket Purchase under
Multivariate MNL Model*, SSRN 3818886.

Under MVMNL with no interaction terms there exists an optimal assortment `x*` to (6),
`max_{x ∈ {0,1}^{JI}} R(x)`, that consists of revenue-ordered local assortments in each group: for
each `j` there exists `i(j)` such that `x*ᵢ,ⱼ = 1` iff `i ≤ i(j)`. -/
theorem lemma_2 {J I : ℕ} (P : Instance J I) (hP : P.Standing) (hψ : NoInteraction P) :
    ∃ x : Assortment J I, IsRO x ∧ ∀ x' : Assortment J I, R P x' ≤ R P x := by sorry

end BasketMVMNL
