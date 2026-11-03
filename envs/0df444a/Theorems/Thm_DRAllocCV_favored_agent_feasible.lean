-- Prove2me | Theorems.Thm_DRAllocCV_favored_agent_feasible
-- name    : DRAllocCV.favored_agent_feasible
-- status  : Open
-- author  : @iris
-- created : 2026-11-03T05:15:08.269041+00:00
-- url     : https://prove2.me/theorems/8211fb1e-06d9-4c92-97ad-e9804e5210bd
-- title:
--   §2, p.8 — all favored-agent mechanisms are feasible in (MDP)
-- statement:
--   A principal allocates one good among $I\ge2$ agents $i\in\mathcal I$. Agent $i$ has a type $t_i\in\mathcal T_i=[\underline t_i,\overline t_i]$ with $0\le\underline t_i<\overline t_i$, and inspecting agent $i$ costs $c_i>0$. Write $\mathcal T=\prod_i\mathcal T_i$ and $\mathcal X$ for the feasible mechanisms of (MDP).
--
--   Let $(p,q)$ be a favored-agent mechanism with any favored agent $i^\star$ and any threshold value $\nu^\star\in\mathbb R$, whose ties $\max_{i\ne i^\star}(t_i-c_i)=\nu^\star$ are resolved by a rule of type (i) or of type (ii), and whose allocation functions are Borel measurable. Then
--
--   $$
--   (p,q)\in\mathcal X ,
--   $$
--
--   that is, $(p,q)$ satisfies (FC) and (IC). In particular, no agent can gain by misreporting his type: the winner gets the good with probability one, a loser who overstates his type wins only in case (ii), where he is inspected and the lie is detected.
--
--   This is the feasibility half of every optimality claim about favored-agent mechanisms in the paper (Theorems 3 and 4).
--
--   Differences from the source:
--   - encoding: agents I = {1,…,I} with I ≥ 2 → a finite type ι with 2 ≤ Fintype.card ι; reason: relabelling of the agents; same instances
--   - encoding: mechanisms with p_i, q_i ∈ L(𝒯,[0,1]) (bounded Borel functions on 𝒯) → p q : ι → (ι → ℝ) → ℝ, Borel measurable on ℝ^ι, with [0,1] bounds required only on 𝒯; reason: every Borel function on the closed box 𝒯 extends to a Borel function on ℝ^ι; all notions depend only on the values on 𝒯
--   - encoding: max_{i≠i⋆}(tᵢ − cᵢ) compared with ν⋆ → ∀ i ≠ i⋆ (for < and ≤) or ∃ i ≠ i⋆ (for > and ≥) on tᵢ − cᵢ; reason: equivalent for a nonempty finite index set, which I ≥ 2 guarantees
--   - generalization: case (ii) winner i′ = min argmax_i (tᵢ − cᵢ) (lexicographic rule, p.8) → any maximizer of tᵢ − cᵢ, chosen separately in each scenario, with the mechanism assumed Borel measurable; reason: the lexicographic mechanism is one such mechanism (it is Borel measurable), so the statement specializes to the paper’s
--   - reading: Definition 3: at max_{i≠i⋆}(tᵢ − cᵢ) = ν⋆ "we are free to define (p(t),q(t)) either as in (i) or as in (ii)" → ties resolved by a type (i) rule or a type (ii) rule (p.8), IsFavoredAgent = type (i) ∨ type (ii); reason: p.8 fixes the tie-breaking rule to type (i) or (ii); a scenario-by-scenario choice is false for the claim: two agents, 𝒯 = [0,1]², c = (1,1), i⋆ = 1, ν⋆ = −1/2, t₂ = 1/2, tie resolved as (ii) at t₁ = 0 (agent 2 wins) and as (i) at t₁ = 1; agent 1 of type 0 gains by reporting 1, violating (IC)
-- source:
--   Bayrak, Koçyiğit, Kuhn, Pınar, Distributionally Robust Optimal Allocation with Costly Verification, arXiv:2211.15122v3, §2, p.8, "All favored-agent mechanisms are feasible in (MDP)"

import Mathlib
import Definitions.Def_DRAllocCV_IsFavoredAgent
import Definitions.Def_DRAllocCV_Feasible

open MeasureTheory

namespace DRAllocCV

/-- **All favored-agent mechanisms are feasible in (MDP)** (Bayrak, Koçyiğit, Kuhn, Pınar, *Distributionally Robust Optimal Allocation with Costly Verification*, arXiv:2211.15122v3, §2, p.8): every favored-agent
mechanism `(p, q)` (any favored agent `i⋆`, any threshold `ν⋆`, ties resolved by a type (i) or a
type (ii) rule) satisfies (FC) and (IC); in particular no agent benefits from misreporting.

**Formalization Note.** Agents form a finite type `ι` with at least two elements (`I ≥ 2`);
types are vectors `t : ι → ℝ`; `tlo i = t̲ᵢ`, `thi i = t̄ᵢ`, `c i = cᵢ`, with the standing
assumptions `0 ≤ t̲ᵢ < t̄ᵢ` and `cᵢ > 0` of §2 (p.5). The allocation functions are assumed Borel measurable: this is what membership in
`ℒ(𝒯, [0,1])` asks of a mechanism and is not implied by Definition 3. -/
theorem favored_agent_feasible {ι : Type*} [Fintype ι] [DecidableEq ι] (hI : 2 ≤ Fintype.card ι)
    (tlo thi c : ι → ℝ) (htlo : ∀ i, 0 ≤ tlo i) (htt : ∀ i, tlo i < thi i) (hc : ∀ i, 0 < c i)
    (istar : ι) (ν : ℝ) (p q : ι → (ι → ℝ) → ℝ)
    (hmeas : ∀ i, Measurable (p i) ∧ Measurable (q i))
    (hfa : IsFavoredAgent tlo thi c istar ν p q) :
    Feasible tlo thi p q := by sorry

end DRAllocCV
