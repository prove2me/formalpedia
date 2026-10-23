-- Prove2me | Theorems.Thm_DisclosureStatics_Aggregation_proposition_1
-- name    : DisclosureStatics.Aggregation.proposition_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-22T07:15:54.04904+00:00
-- url     : https://prove2.me/theorems/4bf294d5-23eb-440c-98c2-26c42a36fc26
-- title:
--   Proposition 1 (corrected), p. 23 — the aggregation effect on the insurer's loss is strictly positive
-- statement:
--   Assume the standing assumptions, Assumption 1 ($u(x)=(1-e^{-\gamma x})/\gamma$, $\gamma>0$) and Assumption 2 on $(-\infty,1/\gamma)$. Let $\pi$ be a PDS, and let $B$ be the union of a family $\mathcal S$ of at least two events of $\pi$, none equal to $\{s_1\}$, such that not all events of $\mathcal S$ have the same probability-adjusted price $r_S$. Let $c$ solve (DP-$\pi$) and let $c^*$ solve the intermediate problem (DP-B) given $c$. Then the aggregation effect $\Delta L^*=L(c^*)-L(c)$ on the insurer's expected loss satisfies
--   $$\Delta L^*=\sum_{s_i\in B}P(s_i)\,(c^*_i-c_i)>0.$$
--
--   The aggregation effect is the first half of the decomposition $\Delta L=\Delta L^*+\Delta\tilde L$ of §2.5; together with Proposition 2 it yields Theorem 1.
--
--   **Formalization Note** The printed statement has a middle expression, $\Delta L^*=\frac{P(B)}{\gamma}\Bigl(1-\frac{\sum_{S_k\in B}P(S_k\mid B)\varphi'(V_{S_k}(s))}{\sum_{S_k\in B}\frac{p_{S_k}}{p_B}\varphi'(V_{S_k}(s))}\Bigr)$. It is a first-order approximation printed as an equality (for the paper's Example 1 the exact $\Delta L^*$ is $0.0045630$ and the expression gives $0.0045940$), so it is omitted. The hypothesis that the merged events do not all share one price $r_S$ is added: if they do, $c^*=c$ and $\Delta L^*=0$, so the strict inequality fails; the paper's p. 21 ranks events strictly, $r_{S_2}<\dots<r_{S_N}$.
-- source:
--   Burkovskaya & Li, Comparative Profitability of Product Disclosure Statements, SSRN 3532175 (version of February 4, 2020), p. 23, Proposition 1

import Mathlib
import Definitions.Def_DisclosureStatics_Aggregation_Model

namespace DisclosureStatics.Aggregation

/-- Proposition 1, p. 23, without its approximate middle expression. -/
theorem proposition_1 {Ω : Type*} [Fintype Ω] [DecidableEq Ω]
    (M : Market Ω) (hM : M.Standing) (γ : ℝ) (hγ : 0 < γ)
    (φ : ℝ → ℝ) (hφ : AggregationAverse φ (Set.Iio (1 / γ)))
    (π : PDS Ω) (hπ : IsPDS M π) (𝒮 : Finset (Finset Ω)) (B : Finset Ω)
    (hB : IsMergedEvent M π 𝒮 B)
    (hhet : ∃ S ∈ 𝒮, ∃ S' ∈ 𝒮, rE M S ≠ rE M S')
    (c cs : Ω → ℝ) (hc : IsDemand M (cara γ) φ π c)
    (hcs : IsIntermediate M (cara γ) φ B c cs) :
    Loss M cs - Loss M c = ∑ i ∈ B, M.P i * (cs i - c i) ∧ 0 < Loss M cs - Loss M c := by sorry
end DisclosureStatics.Aggregation
