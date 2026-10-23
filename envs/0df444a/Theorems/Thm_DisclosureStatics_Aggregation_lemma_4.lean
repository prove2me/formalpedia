-- Prove2me | Theorems.Thm_DisclosureStatics_Aggregation_lemma_4
-- name    : DisclosureStatics.Aggregation.lemma_4
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-22T07:15:27.993044+00:00
-- url     : https://prove2.me/theorems/1f933cc7-3abc-4e5b-88f8-bc50268471d5
-- title:
--   Lemma 4, p. 25 — under CARA u the event-smoothing change is constant within each event of ρ
-- statement:
--   Assume the standing assumptions and Assumption 1, $u(x)=(1-e^{-\gamma x})/\gamma$ with $\gamma>0$; of $\varphi$ assume only regularity on $(-\infty,1/\gamma)$: $C^3$ with $\varphi'>0$. Let $\rho$ be obtained from the PDS $\pi$ by merging a family $\mathcal S$ of at least two events of $\pi$ (none equal to $\{s_1\}$) into one event $B$. Let $c$ solve (DP-$\pi$), $c^*$ solve (DP-B) given $c$, and $\tilde c$ solve (DP-$\rho$). Then for every event $S_k\in\rho$ and all $s_i,s_j\in S_k$,
--   $$\Delta\tilde c_i=\Delta\tilde c_j,\qquad \Delta\tilde c_i=\tilde c_i-c^*_i .$$
--
--   This common value is the paper's $\Delta\tilde c_{S_k}$, the event-smoothing change of event $S_k$, which Lemma 5 ranks.
--
--   **Formalization Note** Assumption 2 is not used, as on the page. The conclusion is stated as equality of the changes within each event; the notation $\Delta\tilde c_{S_k}$ is not introduced in Lean.
-- source:
--   Burkovskaya & Li, Comparative Profitability of Product Disclosure Statements, SSRN 3532175 (version of February 4, 2020), p. 25, Lemma 4

import Mathlib
import Definitions.Def_DisclosureStatics_Aggregation_Model

namespace DisclosureStatics.Aggregation

/-- Lemma 4, p. 25 (Assumption 1 only; `φ` merely regular). -/
theorem lemma_4 {Ω : Type*} [Fintype Ω] [DecidableEq Ω]
    (M : Market Ω) (hM : M.Standing) (γ : ℝ) (hγ : 0 < γ)
    (φ : ℝ → ℝ) (hφ : Regular φ (Set.Iio (1 / γ)))
    (π ρ : PDS Ω) (hπ : IsPDS M π) (𝒮 : Finset (Finset Ω)) (B : Finset Ω)
    (hagg : IsOneStepAggregation M π ρ 𝒮 B)
    (c cs ct : Ω → ℝ) (hc : IsDemand M (cara γ) φ π c)
    (hcs : IsIntermediate M (cara γ) φ B c cs) (hct : IsDemand M (cara γ) φ ρ ct) :
    ∀ S ∈ ρ.parts, ∀ i ∈ S, ∀ j ∈ S, ct i - cs i = ct j - cs j := by sorry
end DisclosureStatics.Aggregation
