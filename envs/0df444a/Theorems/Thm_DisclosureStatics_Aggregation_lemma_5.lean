-- Prove2me | Theorems.Thm_DisclosureStatics_Aggregation_lemma_5
-- name    : DisclosureStatics.Aggregation.lemma_5
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-22T07:15:40.275361+00:00
-- url     : https://prove2.me/theorems/2b99b2c5-89dc-4dc0-801c-393ad7a08621
-- title:
--   Lemma 5, p. 26 — outside B, higher-valued events gain more in the event-smoothing stage
-- statement:
--   Assume the standing assumptions, Assumption 1 ($u(x)=(1-e^{-\gamma x})/\gamma$, $\gamma>0$) and Assumption 2 on $(-\infty,1/\gamma)$. Let $\rho$ be obtained from the PDS $\pi$ by merging a family $\mathcal S$ of at least two events of $\pi$ (none equal to $\{s_1\}$, not all with the same price $r_S$) into one event $B$. Let $c$ solve (DP-$\pi$), $c^*$ solve (DP-B) given $c$, and $\tilde c$ solve (DP-$\rho$), and write $\Delta\tilde c_i=\tilde c_i-c^*_i$. Then for any two events $S_k,S_l\in\rho$ different from $B$ (so contained in $B^c$; $\{s_1\}$ is allowed) and any $s_i\in S_k$, $s_j\in S_l$,
--   $$V_{S_k}(c)>V_{S_l}(c)\iff \Delta\tilde c_i>\Delta\tilde c_j .$$
--
--   By Lemma 4 the changes $\Delta\tilde c$ are constant on each event, so this ranks the event-smoothing changes $\Delta\tilde c_{S_k}$ outside $B$ by the events' values, and by Lemma 1 by their prices.
--
--   **Formalization Note** $V_{S_k}$ is evaluated at the original solution $c$, which coincides with $c^*$ outside $B$. The hypothesis that the merged events do not all share one price is added: otherwise every $\Delta\tilde c$ vanishes and the equivalence fails for events of different value.
-- source:
--   Burkovskaya & Li, Comparative Profitability of Product Disclosure Statements, SSRN 3532175 (version of February 4, 2020), p. 26, Lemma 5

import Mathlib
import Definitions.Def_DisclosureStatics_Aggregation_Model

namespace DisclosureStatics.Aggregation

/-- Lemma 5, p. 26. -/
theorem lemma_5 {Ω : Type*} [Fintype Ω] [DecidableEq Ω]
    (M : Market Ω) (hM : M.Standing) (γ : ℝ) (hγ : 0 < γ)
    (φ : ℝ → ℝ) (hφ : AggregationAverse φ (Set.Iio (1 / γ)))
    (π ρ : PDS Ω) (hπ : IsPDS M π) (𝒮 : Finset (Finset Ω)) (B : Finset Ω)
    (hagg : IsOneStepAggregation M π ρ 𝒮 B)
    (hhet : ∃ S ∈ 𝒮, ∃ S' ∈ 𝒮, rE M S ≠ rE M S')
    (c cs ct : Ω → ℝ) (hc : IsDemand M (cara γ) φ π c)
    (hcs : IsIntermediate M (cara γ) φ B c cs) (hct : IsDemand M (cara γ) φ ρ ct) :
    ∀ S ∈ ρ.parts, S ≠ B → ∀ S' ∈ ρ.parts, S' ≠ B → ∀ i ∈ S, ∀ j ∈ S',
      (V M (cara γ) S' c < V M (cara γ) S c ↔ ct j - cs j < ct i - cs i) := by sorry
end DisclosureStatics.Aggregation
