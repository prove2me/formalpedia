-- Prove2me | Theorems.Thm_DisclosureStatics_Aggregation_proposition_2
-- name    : DisclosureStatics.Aggregation.proposition_2
-- status  : Disproved
-- author  : @mikedeng1
-- created : 2026-10-22T07:15:35.054252+00:00
-- url     : https://prove2.me/theorems/16fb2dac-7744-4533-8ced-c889b89a1607
-- title:
--   Proposition 2, p. 26 — if r_B ≥ r_1 ≥ 1 the event-smoothing effect strictly raises the expected loss
-- statement:
--   Assume the standing assumptions, Assumption 1 ($u(x)=(1-e^{-\gamma x})/\gamma$, $\gamma>0$) and Assumption 2 on $(-\infty,1/\gamma)$. Let $\rho$ be obtained from the PDS $\pi$ by merging a family $\mathcal S$ of at least two events of $\pi$ (none equal to $\{s_1\}$, not all with the same price $r_S$) into one event $B$. Let $c$ solve (DP-$\pi$), $c^*$ solve (DP-B) given $c$, and $\tilde c$ solve (DP-$\rho$). If
--   $$r_B\ \ge\ r_1\ \ge\ 1,\qquad r_B=\frac{p_B}{P(B)},\ r_1=\frac{p_1}{P(s_1)},$$
--   then the event-smoothing effect on the insurer's expected loss is strictly positive:
--   $$\Delta\tilde L=L(\tilde c)-L(c^*)>0 .$$
--
--   Together with Proposition 1 this gives Theorem 1.
--
--   **Formalization Note** The hypothesis that the merged events do not all share one price is added: otherwise $\tilde c=c^*$ and $\Delta\tilde L=0$.
-- source:
--   Burkovskaya & Li, Comparative Profitability of Product Disclosure Statements, SSRN 3532175 (version of February 4, 2020), p. 26, Proposition 2

import Mathlib
import Definitions.Def_DisclosureStatics_Aggregation_Model

namespace DisclosureStatics.Aggregation

/-- Proposition 2, p. 26. -/
theorem proposition_2 {Ω : Type*} [Fintype Ω] [DecidableEq Ω]
    (M : Market Ω) (hM : M.Standing) (γ : ℝ) (hγ : 0 < γ)
    (φ : ℝ → ℝ) (hφ : AggregationAverse φ (Set.Iio (1 / γ)))
    (π ρ : PDS Ω) (hπ : IsPDS M π) (𝒮 : Finset (Finset Ω)) (B : Finset Ω)
    (hagg : IsOneStepAggregation M π ρ 𝒮 B)
    (hhet : ∃ S ∈ 𝒮, ∃ S' ∈ 𝒮, rE M S ≠ rE M S')
    (hrB : rE M {M.s₁} ≤ rE M B) (hr1 : 1 ≤ rE M {M.s₁})
    (c cs ct : Ω → ℝ) (hc : IsDemand M (cara γ) φ π c)
    (hcs : IsIntermediate M (cara γ) φ B c cs) (hct : IsDemand M (cara γ) φ ρ ct) :
    Loss M cs < Loss M ct := by sorry
end DisclosureStatics.Aggregation
