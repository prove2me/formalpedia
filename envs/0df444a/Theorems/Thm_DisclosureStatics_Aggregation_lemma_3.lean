-- Prove2me | Theorems.Thm_DisclosureStatics_Aggregation_lemma_3
-- name    : DisclosureStatics.Aggregation.lemma_3
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-22T07:15:32.25476+00:00
-- url     : https://prove2.me/theorems/59ed6bec-b0ad-482a-9a1b-e5df199c0382
-- title:
--   Lemma 3, p. 24 — λ_B < λ_ρ < λ_π, and event smoothing moves consumption out of B
-- statement:
--   Assume the standing assumptions, Assumption 1 ($u(x)=(1-e^{-\gamma x})/\gamma$, $\gamma>0$) and Assumption 2 on $(-\infty,1/\gamma)$. Let $\rho$ be obtained from the PDS $\pi$ by merging a family $\mathcal S$ of at least two events of $\pi$ (none equal to $\{s_1\}$, not all with the same price $r_S$) into one event $B$. Let $c$ solve (DP-$\pi$), $c^*$ solve (DP-B) given $c$, and $\tilde c$ solve (DP-$\rho$), and let $\lambda_\pi$, $\lambda_B$, $\lambda_\rho$ be multipliers for which $c$, $c^*$, $\tilde c$ satisfy the first-order conditions (1), (3), (2) respectively. Then
--   $$\lambda_B<\lambda_\rho<\lambda_\pi,$$
--   and, writing $\Delta\tilde c_i=\tilde c_i-c^*_i$, we have $\Delta\tilde c_i<0$ for every $s_i\in B$ and $\Delta\tilde c_j>0$ for every $s_j\notin B$ (including $s_1$).
--
--   The lemma gives the direction of the event-smoothing effect: income moves from the merged event to the rest of the disclosure statement.
--
--   **Formalization Note** The hypothesis that the merged events do not all share one price is added: otherwise $c^*=c=\tilde c$ and every strict inequality fails. The multipliers are hypothesized; by the FOC characterization they exist and are unique.
-- source:
--   Burkovskaya & Li, Comparative Profitability of Product Disclosure Statements, SSRN 3532175 (version of February 4, 2020), p. 24, Lemma 3

import Mathlib
import Definitions.Def_DisclosureStatics_Aggregation_Model

namespace DisclosureStatics.Aggregation

/-- Lemma 3, p. 24. -/
theorem lemma_3 {Ω : Type*} [Fintype Ω] [DecidableEq Ω]
    (M : Market Ω) (hM : M.Standing) (γ : ℝ) (hγ : 0 < γ)
    (φ : ℝ → ℝ) (hφ : AggregationAverse φ (Set.Iio (1 / γ)))
    (π ρ : PDS Ω) (hπ : IsPDS M π) (𝒮 : Finset (Finset Ω)) (B : Finset Ω)
    (hagg : IsOneStepAggregation M π ρ 𝒮 B)
    (hhet : ∃ S ∈ 𝒮, ∃ S' ∈ 𝒮, rE M S ≠ rE M S')
    (c cs ct : Ω → ℝ) (hc : IsDemand M (cara γ) φ π c)
    (hcs : IsIntermediate M (cara γ) φ B c cs) (hct : IsDemand M (cara γ) φ ρ ct)
    (lπ lB lρ : ℝ) (hlπ : IsFOC M (cara γ) φ π c lπ) (hlB : IsFOCB M (cara γ) φ B cs lB)
    (hlρ : IsFOC M (cara γ) φ ρ ct lρ) :
    lB < lρ ∧ lρ < lπ ∧ (∀ i ∈ B, ct i - cs i < 0) ∧ (∀ j ∉ B, 0 < ct j - cs j) := by sorry
end DisclosureStatics.Aggregation
