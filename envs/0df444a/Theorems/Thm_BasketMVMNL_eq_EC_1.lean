-- Prove2me | Theorems.Thm_BasketMVMNL_eq_EC_1
-- name    : BasketMVMNL.eq_EC_1
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T10:31:37.445989+00:00
-- url     : https://prove2.me/theorems/d0d531ce-7b1e-4c66-b1a4-d635e42a93a4
-- title:
--   (EC.1) — with the other groups fixed, $R$ is linear-fractional in the local assortment
-- statement:
--   Under MVMNL with no interaction terms and the standing assumptions of §4, fix an assortment $x$ and a group $j$, and let
--   $$
--   A_1=B_1=\prod_{j'\neq j}\gamma_{j'}(x_{j'}),\qquad A_2=A_3=\sum_{j'\neq j}\Lambda_{j'}(x_{j'})\prod_{j''\notin\{j,j'\}}\gamma_{j''}(x_{j''}),\qquad B_2=B_1+v_0-1,
--   $$
--   with $\Lambda_{j'}(x_{j'})=\sum_i r_{i,j'}v_{i,j'}x_{i,j'}$. Then $A_1=B_1>0$, $A_2=A_3\ge0$ and $B_2\ge0$, and for every local assortment $z\in\{0,1\}^I$ of group $j$ (the other groups kept as in $x$)
--   $$
--   R(x\text{ with }x_j:=z)=\frac{\sum_i(A_1r_{i,j}+A_2)\,v_{i,j}z_i+A_3}{\sum_i B_1\,v_{i,j}z_i+B_2}.
--   $$
--   So, with the other groups fixed, optimizing (6) over group $j$ is the linear-fractional problem $\max_{z}F(z)$; this is the first step of the proof of Lemma 2.
--
--   Differences from the source:
--
--   - encoding: J groups of I products indexed (i,j) from 1; bundles y with yⱼ ∈ {0,1,…,I}; x ∈ {0,1}^{JI}; utilities θᵢ,ⱼ, μ₀ with vᵢ,ⱼ = exp θᵢ,ⱼ, v₀ = exp μ₀ → groups Fin J, products Fin I (0-based); bundles Fin J → Option (Fin I) with none for yⱼ = 0; x : Fin J → Fin I → Bool; the instance stores v, v₀ (θ = log v, μ₀ = log v₀), r and ψ; reason: the same instances, assortments and bundles
--   - encoding: "There are J groups of products and each group consists of I different products" (p.6) → 1 ≤ J and 1 ≤ I in Standing; reason: excludes only the empty instance, which the paper does not consider
--   - reading: rᵢ,ⱼ, "the revenue of product i in group j" (p.7), sign not stated → 0 ≤ rᵢ,ⱼ in Standing; reason: the plain meaning of revenue; with a negative revenue Theorem 1 is false (J = 2, I = 1, v = (0.2768, 10), r = (4.1257, −0.8847), v₀ = 53.3, ϵ = 0.1: Algorithm U1 earns 0.019083 < 0.9 · 0.021315)
--   - encoding: "Without loss of generality, we assume that the products in each group are ordered in such a way that the revenues {rᵢ,ⱼ} are non-increasing in i for each j" (p.9) → Standing.r_antitone: r j is antitone in i for every j; reason: the section's standing assumption; any instance is brought to this form by relabelling the products of each group, and revenue-ordered is defined with respect to this order
--   - reading: (3)–(4) write exp{μ(y)} for every permissible y, while (1) gives y = 0 the utility μ₀ → μ(0) = μ₀ = log v₀, so the empty bundle has weight v₀; reason: the denominator v₀ + … of Lemma 1 fixes this meaning
--   - reading: A∗₁ = B∗₁ := ∏_{m≠j}(1 + Σₙ v_{m,n}x∗_{m,n}), A∗₂ = A∗₃ := Σ_{m≠j,n} r_{m,n}v_{m,n}x∗_{m,n} · ∏_{m′≠m or j,n}(1 + v_{m′,n}x∗_{m′,n}), with m, n playing group and product in turn → A₁ = ∏_{j′≠j} γ_{j′}(x_{j′}), A₂ = Σ_{j′≠j} Λ_{j′}(x_{j′}) ∏_{j′′∉{j,j′}} γ_{j′′}(x_{j′′}); reason: the evident meaning of the garbled indices; it is what substituting into (5) gives
--   - reading: "the optimization (6) reduces into max_{xⱼ} F(xⱼ)" with the A∗ₖ, B∗ₖ "non-negative constants … (both A∗₁ and B∗₁ are strictly positive)" → R(x with xⱼ := z) = F(z) for every z, together with 0 < A₁, 0 ≤ A₂, 0 ≤ A₁ + v₀ − 1; reason: the reduction is the equality of the objectives for every local assortment z
--   - generalization: the optimal x∗ in the groups j′ ≠ j → every assortment x; reason: the identity uses nothing about optimality; at x = x∗ it is the paper's statement
-- source:
--   Jasin, Lyu, Najafi, Zhang, Assortment Optimization with Multi-Item Basket Purchase under Multivariate MNL Model, SSRN 3818886, (EC.1), p.ec2

import Mathlib
import Definitions.Def_BasketMVMNL_Model
import Definitions.Def_BasketMVMNL_Rounding

namespace BasketMVMNL

/-- **Equation (EC.1)**, p.ec2 (proof of Lemma 2). Jasin, Lyu, Najafi, Zhang, *Assortment Optimization with Multi-Item Basket Purchase under
Multivariate MNL Model*, SSRN 3818886.

Fix an assortment `x` and a group `j`, and let
`A₁ = B₁ = ∏_{j'≠j} γ_{j'}(x_{j'})`, `A₂ = A₃ = Σ_{j'≠j} Λ_{j'}(x_{j'}) ∏_{j''∉{j,j'}} γ_{j''}(x_{j''})`
and `B₂ = B₁ + v₀ − 1`. Then `A₁ = B₁ > 0`, `A₂ = A₃ ≥ 0`, `B₂ ≥ 0`, and for every local
assortment `z` of group `j` (the other groups kept as in `x`)
`R(x with xⱼ := z) = (Σᵢ (A₁ rᵢ,ⱼ + A₂) vᵢ,ⱼ zᵢ + A₃) / (Σᵢ B₁ vᵢ,ⱼ zᵢ + B₂)`.

**Formalization Note.** The paper writes the constants for the optimal `x*` with garbled indices
(`m, n` play group and product in turn); this is the evident meaning, stated for every `x`. -/
theorem eq_EC_1 {J I : ℕ} (P : Instance J I) (hP : P.Standing) (hψ : NoInteraction P)
    (x : Assortment J I) (j : Fin J) :
    let A₁ := ∏ j' ∈ Finset.univ.erase j, γ P x j'
    let A₂ := ∑ j' ∈ Finset.univ.erase j, Λ P x j' * ∏ j'' ∈ (Finset.univ.erase j).erase j', γ P x j''
    0 < A₁ ∧ 0 ≤ A₂ ∧ 0 ≤ A₁ + P.v0 - 1 ∧
    ∀ z : Fin I → Bool,
      R P (Function.update x j z) =
        (∑ i, (A₁ * P.r j i + A₂) * P.v j i * bit (z i) + A₂) /
          (∑ i, A₁ * P.v j i * bit (z i) + (A₁ + P.v0 - 1)) := by sorry

end BasketMVMNL
