-- Prove2me | Theorems.Thm_BasketMVMNL_eq_EC_5
-- name    : BasketMVMNL.eq_EC_5
-- status  : Proved
-- author  : @iris
-- created : 2026-10-31T10:31:43.222544+00:00
-- url     : https://prove2.me/theorems/43cb7a17-aae0-4a9e-88a7-fd6f8b7ba955
-- title:
--   (EC.5) — rounding moves each $R_j$ by at most $(1+\epsilon^\prime)^{J-1}$ and $(1+\epsilon^\prime)^J$
-- statement:
--   Under MVMNL with no interaction terms and the standing assumptions of §4, for every $\epsilon'>0$, every assortment $x$ and every group $j$,
--   $$
--   \frac{\bar R_j(x)}{(1+\epsilon')^{J-1}}\le R_j(x)\le\bar R_j(x)\cdot(1+\epsilon')^J,
--   $$
--   where $R_j$ is the $j$-th summand of (7) and $\bar R_j$ is the same summand with every $\gamma$ and $\Gamma$ rounded up to the integer powers $\bar\gamma$, $\bar\Gamma$ of $1+\epsilon'$. Summed over $j$, it bounds the error of replacing $R$ by the rounded objective $\bar R$ that Algorithm U1 maximizes.
--
--   Differences from the source:
--
--   - encoding: J groups of I products indexed (i,j) from 1; bundles y with yⱼ ∈ {0,1,…,I}; x ∈ {0,1}^{JI}; utilities θᵢ,ⱼ, μ₀ with vᵢ,ⱼ = exp θᵢ,ⱼ, v₀ = exp μ₀ → groups Fin J, products Fin I (0-based); bundles Fin J → Option (Fin I) with none for yⱼ = 0; x : Fin J → Fin I → Bool; the instance stores v, v₀ (θ = log v, μ₀ = log v₀), r and ψ; reason: the same instances, assortments and bundles
--   - encoding: "There are J groups of products and each group consists of I different products" (p.6) → 1 ≤ J and 1 ≤ I in Standing; reason: excludes only the empty instance, which the paper does not consider
--   - reading: rᵢ,ⱼ, "the revenue of product i in group j" (p.7), sign not stated → 0 ≤ rᵢ,ⱼ in Standing; reason: the plain meaning of revenue; with a negative revenue Theorem 1 is false (J = 2, I = 1, v = (0.2768, 10), r = (4.1257, −0.8847), v₀ = 53.3, ϵ = 0.1: Algorithm U1 earns 0.019083 < 0.9 · 0.021315)
--   - encoding: "Without loss of generality, we assume that the products in each group are ordered in such a way that the revenues {rᵢ,ⱼ} are non-increasing in i for each j" (p.9) → Standing.r_antitone: r j is antitone in i for every j; reason: the section's standing assumption; any instance is brought to this form by relabelling the products of each group, and revenue-ordered is defined with respect to this order
--   - encoding: (1+ϵ′)^{mⱼ−1} < γⱼ(xⱼ) ≤ (1+ϵ′)^{mⱼ}, mⱼ = 1 if xⱼ = 0; M = maxⱼ ⌈log_{1+ϵ′}(1 + Σᵢ vᵢ,ⱼ)⌉ → mexp ϵ′ γ = least m ≥ 1 with γ ≤ (1+ϵ′)^m; γ̄ = (1+ϵ′)^{mexp}; Mcap = maxⱼ mexp(1 + Σᵢ vᵢ,ⱼ); reason: the same integers for ϵ′ > 0, γ ≥ 1 and 1 + Σᵢ vᵢ,ⱼ > 1
--   - encoding: R̄ⱼ(x) = Σᵢ rᵢ,ⱼvᵢ,ⱼxᵢ,ⱼ · ∏_{j′≠j} γ̄_{j′}(x_{j′})/(Γ̄(x) + v₀ − 1) (EC.3) → R̄ⱼ = (7)'s summand with γ̄, Γ̄ in place of γ, Γ (p.13); reason: the two expressions are equal since Γ̄(x) > 0 and γ̄ⱼ > 0
-- source:
--   Jasin, Lyu, Najafi, Zhang, Assortment Optimization with Multi-Item Basket Purchase under Multivariate MNL Model, SSRN 3818886, (EC.5), p.ec5

import Mathlib
import Definitions.Def_BasketMVMNL_Model
import Definitions.Def_BasketMVMNL_Rounding

namespace BasketMVMNL

/-- **Equation (EC.5)**, p.ec5 (proof of Theorem 1). Jasin, Lyu, Najafi, Zhang, *Assortment Optimization with Multi-Item Basket Purchase under
Multivariate MNL Model*, SSRN 3818886.

For every `ϵ′ > 0`, every assortment `x` and every group `j`,
`R̄ⱼ(x)/(1 + ϵ′)^{J−1} ≤ Rⱼ(x) ≤ R̄ⱼ(x) · (1 + ϵ′)^J`,
where `Rⱼ` is the summand of (7) and `R̄ⱼ` the same with every `γ`, `Γ` rounded up to integer powers
`γ̄`, `Γ̄` of `1 + ϵ′`. -/
theorem eq_EC_5 {J I : ℕ} (P : Instance J I) (hP : P.Standing) (hψ : NoInteraction P)
    (ε' : ℝ) (hε' : 0 < ε') (x : Assortment J I) (j : Fin J) :
    Rbarj ε' P x j / (1 + ε') ^ (J - 1) ≤ Rj P x j ∧ Rj P x j ≤ Rbarj ε' P x j * (1 + ε') ^ J := by sorry

end BasketMVMNL
