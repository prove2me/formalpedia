-- Prove2me | Theorems.Thm_BasketMVMNL_eq_7
-- name    : BasketMVMNL.eq_7
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T10:31:40.51661+00:00
-- url     : https://prove2.me/theorems/f59ccbe7-c62e-47c4-befd-b73f91201783
-- title:
--   (7) — $R(x)=\sum_j R_j(x)$
-- statement:
--   Under MVMNL with no interaction terms and the standing assumptions of §4, for every assortment $x$,
--   $$
--   R(x)=\sum_j\left[\frac{\sum_i r_{i,j}v_{i,j}x_{i,j}}{\big[\frac{v_0-1}{\Gamma(x)}+1\big]\gamma_j(x_j)}\right]=\sum_j R_j(x),
--   $$
--   where $\gamma_j(x_j)=1+\sum_i v_{i,j}x_{i,j}$, $\Gamma(x)=\prod_j\gamma_j(x_j)$ and $R$ is the expected total revenue (4). Once $\Gamma(x)$ is fixed the revenue separates across groups, which is what the dynamic program of Algorithm U1 exploits.
--
--   Differences from the source:
--
--   - encoding: J groups of I products indexed (i,j) from 1; bundles y with yⱼ ∈ {0,1,…,I}; x ∈ {0,1}^{JI}; utilities θᵢ,ⱼ, μ₀ with vᵢ,ⱼ = exp θᵢ,ⱼ, v₀ = exp μ₀ → groups Fin J, products Fin I (0-based); bundles Fin J → Option (Fin I) with none for yⱼ = 0; x : Fin J → Fin I → Bool; the instance stores v, v₀ (θ = log v, μ₀ = log v₀), r and ψ; reason: the same instances, assortments and bundles
--   - encoding: "There are J groups of products and each group consists of I different products" (p.6) → 1 ≤ J and 1 ≤ I in Standing; reason: excludes only the empty instance, which the paper does not consider
--   - reading: rᵢ,ⱼ, "the revenue of product i in group j" (p.7), sign not stated → 0 ≤ rᵢ,ⱼ in Standing; reason: the plain meaning of revenue; with a negative revenue Theorem 1 is false (J = 2, I = 1, v = (0.2768, 10), r = (4.1257, −0.8847), v₀ = 53.3, ϵ = 0.1: Algorithm U1 earns 0.019083 < 0.9 · 0.021315)
--   - encoding: "Without loss of generality, we assume that the products in each group are ordered in such a way that the revenues {rᵢ,ⱼ} are non-increasing in i for each j" (p.9) → Standing.r_antitone: r j is antitone in i for every j; reason: the section's standing assumption; any instance is brought to this form by relabelling the products of each group, and revenue-ordered is defined with respect to this order
--   - reading: (3)–(4) write exp{μ(y)} for every permissible y, while (1) gives y = 0 the utility μ₀ → μ(0) = μ₀ = log v₀, so the empty bundle has weight v₀; reason: the denominator v₀ + … of Lemma 1 fixes this meaning
-- source:
--   Jasin, Lyu, Najafi, Zhang, Assortment Optimization with Multi-Item Basket Purchase under Multivariate MNL Model, SSRN 3818886, (7), p.12

import Mathlib
import Definitions.Def_BasketMVMNL_Model
import Definitions.Def_BasketMVMNL_Rounding

namespace BasketMVMNL

/-- **Equation (7)**, p.12. Jasin, Lyu, Najafi, Zhang, *Assortment Optimization with Multi-Item Basket Purchase under
Multivariate MNL Model*, SSRN 3818886.

Under MVMNL with no interaction terms, for every assortment `x`,
`R(x) = Σⱼ [ Σᵢ rᵢ,ⱼ vᵢ,ⱼ xᵢ,ⱼ / ([(v₀ − 1)/Γ(x) + 1] γⱼ(xⱼ)) ] = Σⱼ Rⱼ(x)`,
where `R` is the expected total revenue (4). -/
theorem eq_7 {J I : ℕ} (P : Instance J I) (hP : P.Standing) (hψ : NoInteraction P)
    (x : Assortment J I) :
    R P x = ∑ j, Rj P x j := by sorry

end BasketMVMNL
