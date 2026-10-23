-- Prove2me | Theorems.Thm_DisclosureStatics_Aggregation_theorem_1
-- name    : DisclosureStatics.Aggregation.theorem_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-22T07:15:39.607856+00:00
-- url     : https://prove2.me/theorems/26872031-11af-4272-b52b-b95d8aba32a4
-- title:
--   Theorem 1, p. 17 (with r_1 ≥ 1 from its proof, p. 27, and a price-heterogeneous B) — aggregating an expensive event strictly raises the expected loss
-- statement:
--   Let the market satisfy the standing assumptions: finitely many states $s_1,\dots,s_n$ with $s_1$ the no-accident state, probabilities $P(s_i)>0$ summing to $1$, Arrow prices $p_i>0$ summing to $1$. Let the consumer have CARA utility $u(x)=(1-e^{-\gamma x})/\gamma$, $\gamma>0$ (Assumption 1), and an aggregation function $\varphi$ that on $u(\mathbb R)=(-\infty,1/\gamma)$ is $C^3$, strictly increasing and strictly concave, with non-increasing absolute aggregation aversion $-\varphi''/\varphi'$ (Assumption 2, CARA or DARA).
--
--   Let $\pi$ be a product disclosure statement (a partition of the states with $\{s_1\}$ as a block), and let $\rho$ be obtained from $\pi$ by merging a family $\mathcal S$ of at least two events of $\pi$, none equal to $\{s_1\}$ and not all with the same probability-adjusted price $r_S=p_S/P(S)$, into one event $B$. Let $c$ solve the insurance demand problem under $\pi$, $\tilde c$ solve it under $\rho$, and $c^*$ solve the intermediate problem (DP-B). Write $L(c)=\sum_{i\ge2}(c_1-c_i)(p_i-P(s_i))$ for the insurer's expected loss. If
--   $$r_B\ \ge\ r_1\ \ge\ 1,$$
--   then
--   $$L(c)<L(\tilde c),\qquad L(c)<L(c^*),\qquad L(c^*)<L(\tilde c),$$
--   that is, aggregation strictly increases the expected loss, and both the aggregation effect $\Delta L^*=L(c^*)-L(c)$ and the event-smoothing effect $\Delta\tilde L=L(\tilde c)-L(c^*)$ are strictly positive.
--
--   This is the paper's main comparative-statics result: an insurer should not merge expensive sections of its disclosure statement.
--
--   **Formalization Note** Two hypotheses are added to the printed theorem. (i) $r_1\ge1$: the paper's proof (p. 27) concludes "as long as $r_B\ge r_1\ge1$", and without it the "moreover" clause is false — with four equiprobable states, $p=(1/5,3/10,1/10,2/5)$, $\gamma=1$, $\varphi(v)=-e^{-v}$, $I=1$, $l_2=l_3=l_4=5/4$, $\pi$ the finest PDS and $B=\{s_2,s_3\}$, one has $r_1=r_B=4/5$, $\Delta L^*\approx0.0604>0$ but $\Delta\tilde L\approx-0.0069<0$. (ii) The merged events do not all share one price: otherwise $c^*=c=\tilde c$ and $\Delta L=0$. Solutions are hypothesized maximizers; their existence and uniqueness is the item `demand_well_defined`.
-- source:
--   Burkovskaya & Li, Comparative Profitability of Product Disclosure Statements, SSRN 3532175 (version of February 4, 2020), p. 17, Theorem 1 (hypothesis r_1 ≥ 1 from its proof, p. 27)

import Mathlib
import Definitions.Def_DisclosureStatics_Aggregation_Model

namespace DisclosureStatics.Aggregation

/-- Theorem 1, p. 17, with `r₁ ≥ 1` (from its proof, p. 27) and a price-heterogeneous `B`. -/
theorem theorem_1 {Ω : Type*} [Fintype Ω] [DecidableEq Ω]
    (M : Market Ω) (hM : M.Standing) (γ : ℝ) (hγ : 0 < γ)
    (φ : ℝ → ℝ) (hφ : AggregationAverse φ (Set.Iio (1 / γ)))
    (π ρ : PDS Ω) (hπ : IsPDS M π) (𝒮 : Finset (Finset Ω)) (B : Finset Ω)
    (hagg : IsOneStepAggregation M π ρ 𝒮 B)
    (hhet : ∃ S ∈ 𝒮, ∃ S' ∈ 𝒮, rE M S ≠ rE M S')
    (hrB : rE M {M.s₁} ≤ rE M B) (hr1 : 1 ≤ rE M {M.s₁})
    (c cs ct : Ω → ℝ) (hc : IsDemand M (cara γ) φ π c)
    (hcs : IsIntermediate M (cara γ) φ B c cs) (hct : IsDemand M (cara γ) φ ρ ct) :
    Loss M c < Loss M ct ∧ Loss M c < Loss M cs ∧ Loss M cs < Loss M ct := by sorry
end DisclosureStatics.Aggregation
