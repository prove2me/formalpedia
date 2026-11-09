-- Prove2me | Theorems.Thm_AutobidSPPE_lemma_2_7
-- name    : AutobidSPPE.lemma_2_7
-- status  : Open
-- author  : @iris
-- created : 2026-11-08T18:03:59.073806+00:00
-- url     : https://prove2.me/theorems/b0649955-55d2-4789-b5fa-eec6c1fdb2e7
-- title:
--   Lemma 2.7 — continuous responses, existence, and finite entry
-- statement:
--   Throughout, $n\ge2$ bidders have independent values $v_i\sim\mathrm{Unif}[0,\bar v_i]$ with $0<\bar v_i$, and budgets $\rho_i>0$.
--
--   1. Each capped endpoint response $\mathsf b_i$ is continuous on the full action box $\prod_j[0,\bar v_j]$ and satisfies the floor
--   $$
--   \mathsf b_i(y_{-i})\ \ge\ \min\{\bar v_i,4\rho_i\}=2\underline y_i .
--   $$
--   2. The endpoint response map has a fixed point in $\prod_j[0,\bar v_j]$, and a profile $y$ of that box is a fixed point if and only if for every $i$
--   $$
--   0<y_i\le\bar v_i,\qquad \mathsf s_i(y)\le\rho_i,\qquad y_i<\bar v_i\implies \mathsf s_i(y)=\rho_i. \tag{23}
--   $$
--   3. The box $\mathcal Y=\prod_i[\underline y_i,\bar v_i]$ is invariant under every averaged response update $y_i\mapsto(1-\tau_i)y_i+\tau_i\mathsf b_i(y_{-i})$ with $0<\tau_i\le1$.
--   4. For such steps, every initialization $y^{(0)}\in\prod_i[0,\bar v_i]$ of the endpoint dynamics (8) satisfies $y^{(t)}\in\mathcal Y$ for every $t\ge T_0=\lceil\log2/\tau_{\min}\rceil$.
--
--   The lemma supplies existence of the equilibrium and the finite transient after which all later estimates apply.
--
--   **Formalization Note** "Enters $\mathcal Y$ by time $T_0$" is stated as membership at every $t\ge T_0$, equivalent given the invariance of item 3.
--
--   Differences from the source:
--   - encoding: every initialization enters 𝒴 by time T₀ → y⁽ᵗ⁾ ∈ 𝒴 for every t ≥ T₀; reason: equivalent given the invariance clause of the same lemma, which is also stated
--   - encoding: max in the response (5)/(7) → sSup of the feasible set; reason: the feasible set is a nonempty bounded closed interval (Lemma 2.7), so its supremum is its maximum
--   - encoding: bidders 1, …, n in a fixed order → bidders Fin n in their natural order, paper bidder i = index i − 1; reason: relabeling; every ordering is a relabeling of Fin n, and no instance changes
-- source:
--   Chen–Morgenstern–Yang, Convergent Dynamics in Second Price Autobidding Games, STOC 2027 submission (manuscript sha256 185cb93f…77659a6), Lemma 2.7, p.14

import Mathlib
import Definitions.Def_AutobidSPPE_endpointSpend
import Definitions.Def_AutobidSPPE_endpointResponse
import Definitions.Def_AutobidSPPE_endpointFloor
import Definitions.Def_AutobidSPPE_endpointBox
import Definitions.Def_AutobidSPPE_endpointIterate
import Definitions.Def_AutobidSPPE_T0

namespace AutobidSPPE

/-- Lemma 2.7, p.14 (Chen–Morgenstern–Yang, *Convergent Dynamics in Second Price Autobidding Games*, STOC 2027 submission manuscript (sha256 185cb93f…77659a6)): the largest feasible endpoint response `𝖻ᵢ` is continuous on the full
rival action box `∏ⱼ[0, v̄ⱼ]` and obeys `𝖻ᵢ(y₋ᵢ) ≥ min{v̄ᵢ, 4ρᵢ} = 2y̲ᵢ`; its fixed points exist
and are exactly the profiles with `0 < yᵢ ≤ v̄ᵢ`, `𝗌ᵢ(y) ≤ ρᵢ`, `yᵢ < v̄ᵢ ⇒ 𝗌ᵢ(y) = ρᵢ` (23); the box
`𝒴` is invariant under every averaged response update with `0 < τᵢ ≤ 1`; and every initialization
in `∏ᵢ[0, v̄ᵢ]` is in `𝒴` at every time `t ≥ T₀ = ⌈log 2/τ_min⌉` (24).

**Formalization Note** "Enters `𝒴` by time `T₀`" is stated as membership at every `t ≥ T₀`, which
the invariance clause makes equivalent. -/
theorem lemma_2_7 {n : ℕ} (hn : 2 ≤ n) (vbar ρ : Fin n → ℝ) (hvbar : ∀ i, 0 < vbar i) (hρ : ∀ i, 0 < ρ i) :
    (∀ i, ContinuousOn (fun y => endpointResponse vbar ρ y i) (Set.Icc 0 vbar)) ∧
    (∀ y ∈ Set.Icc 0 vbar, ∀ i, min (vbar i) (4 * ρ i) ≤ endpointResponse vbar ρ y i) ∧
    (∀ i, min (vbar i) (4 * ρ i) = 2 * endpointFloor vbar ρ i) ∧
    (∃ y ∈ Set.Icc 0 vbar, ∀ i, endpointResponse vbar ρ y i = y i) ∧
    (∀ y ∈ Set.Icc 0 vbar, (∀ i, endpointResponse vbar ρ y i = y i) ↔
      ∀ i, 0 < y i ∧ y i ≤ vbar i ∧ endpointSpend y i ≤ ρ i ∧
        (y i < vbar i → endpointSpend y i = ρ i)) ∧
    (∀ τ : Fin n → ℝ, (∀ i, 0 < τ i ∧ τ i ≤ 1) → ∀ y ∈ endpointBox vbar ρ,
      (fun i => (1 - τ i) * y i + τ i * endpointResponse vbar ρ y i) ∈ endpointBox vbar ρ) ∧
    (∀ τ : Fin n → ℝ, (∀ i, 0 < τ i ∧ τ i ≤ 1) → ∀ y0 ∈ Set.Icc 0 vbar, ∀ t : ℕ, T0 τ ≤ t →
      endpointIterate vbar ρ τ y0 t ∈ endpointBox vbar ρ) := by sorry

end AutobidSPPE
