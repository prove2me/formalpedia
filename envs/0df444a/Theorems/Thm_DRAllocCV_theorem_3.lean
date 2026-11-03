-- Prove2me | Theorems.Thm_DRAllocCV_theorem_3
-- name    : DRAllocCV.theorem_3
-- status  : Open
-- author  : @iris
-- created : 2026-11-03T05:15:15.964497+00:00
-- url     : https://prove2.me/theorems/8de42999-63cd-47fc-a3f1-eb753724cb63
-- title:
--   Theorem 3 — favored-agent mechanisms with $i^\star\in\arg\max\underline\mu_i$, $\nu^\star\ge\overline t_{i^\star}$ are optimal
-- statement:
--   A principal allocates one good among $I\ge2$ agents $i\in\mathcal I$. Agent $i$ has a type $t_i\in\mathcal T_i=[\underline t_i,\overline t_i]$ with $0\le\underline t_i<\overline t_i$, and inspecting agent $i$ costs $c_i>0$. Write $\mathcal T=\prod_i\mathcal T_i$ and $\mathcal X$ for the feasible mechanisms of (MDP). Let $\mathcal P=\{\mathbb P\in\mathcal P_0(\mathcal T):\mathbb E_{\mathbb P}[\tilde t_i]\in[\underline\mu_i,\overline\mu_i]\ \forall i\}$ be a Markov ambiguity set (5) with $\underline t_i<\underline\mu_i<\overline\mu_i<\overline t_i$ for all $i$.
--
--   Then every favored-agent mechanism $(p,q)$ with favored agent
--
--   $$
--   i^\star\in\arg\max_{i\in\mathcal I}\underline\mu_i\qquad\text{and threshold value}\qquad \nu^\star\ge\overline t_{i^\star}
--   $$
--
--   is optimal in (MDP): its worst-case expected payoff over $\mathcal P$ equals $z^\star=\max_i\underline\mu_i$. This holds for either tie-breaking type and for every threshold above $\overline t_{i^\star}$, so (MDP) has infinitely many optimal mechanisms.
--
--   The bound $\overline t_{i^\star}$ is sharp (Remark 2): smaller thresholds can be strictly suboptimal.
--
--   Differences from the source:
--   - encoding: agents I = {1,…,I} with I ≥ 2 → a finite type ι with 2 ≤ Fintype.card ι; reason: relabelling of the agents; same instances
--   - encoding: mechanisms with p_i, q_i ∈ L(𝒯,[0,1]) (bounded Borel functions on 𝒯) → p q : ι → (ι → ℝ) → ℝ, Borel measurable on ℝ^ι, with [0,1] bounds required only on 𝒯; reason: every Borel function on the closed box 𝒯 extends to a Borel function on ℝ^ι; all notions depend only on the values on 𝒯
--   - encoding: distributions P ∈ 𝒫₀(𝒯) → probability measures P on ℝ^ι with P(𝒯ᶜ) = 0; reason: 𝒯 is closed, so these are exactly the Borel probability distributions on 𝒯
--   - encoding: optimal: worst-case expected payoff inf_P E_P equals z⋆ = sup inf → IsOptimal: feasible, and every lower bound of a competitor’s expected payoffs over 𝒫 is a lower bound of its own; reason: equivalent comparison of the infima in the extended reals, without a real ⨅ that would be junk on empty or unbounded sets
--   - encoding: i⋆ ∈ arg max_i µ̲ᵢ → ∀ i, µ̲ᵢ ≤ µ̲ᵢ⋆; reason: equivalent
--   - encoding: max_{i≠i⋆}(tᵢ − cᵢ) compared with ν⋆ → ∀ i ≠ i⋆ (for < and ≤) or ∃ i ≠ i⋆ (for > and ≥) on tᵢ − cᵢ; reason: equivalent for a nonempty finite index set, which I ≥ 2 guarantees
--   - generalization: case (ii) winner i′ = min argmax_i (tᵢ − cᵢ) (lexicographic rule, p.8) → any maximizer of tᵢ − cᵢ, chosen separately in each scenario, with the mechanism assumed Borel measurable; reason: the lexicographic mechanism is one such mechanism (it is Borel measurable), so the statement specializes to the paper’s
--   - reading: Definition 3: at max_{i≠i⋆}(tᵢ − cᵢ) = ν⋆ "we are free to define (p(t),q(t)) either as in (i) or as in (ii)" → ties resolved by a type (i) rule or a type (ii) rule (p.8), IsFavoredAgent = type (i) ∨ type (ii); reason: p.8 fixes the tie-breaking rule to type (i) or (ii); a scenario-by-scenario choice is false for the claim: two agents, 𝒯 = [0,1]², c = (1,1), i⋆ = 1, ν⋆ = −1/2, t₂ = 1/2, tie resolved as (ii) at t₁ = 0 (agent 2 wins) and as (i) at t₁ = 1; agent 1 of type 0 gains by reporting 1, violating (IC)
-- source:
--   Bayrak, Koçyiğit, Kuhn, Pınar, Distributionally Robust Optimal Allocation with Costly Verification, arXiv:2211.15122v3, §4, p.14, Theorem 3

import Mathlib
import Definitions.Def_DRAllocCV_markovSet
import Definitions.Def_DRAllocCV_IsFavoredAgent
import Definitions.Def_DRAllocCV_IsOptimal

open MeasureTheory

namespace DRAllocCV

/-- **Theorem 3** (Bayrak, Koçyiğit, Kuhn, Pınar, *Distributionally Robust Optimal Allocation with Costly Verification*, arXiv:2211.15122v3, §4, p.14). If `𝒫` is a Markov ambiguity set of the form (5), then any
favored-agent mechanism with favored agent `i⋆ ∈ argmax_{i ∈ ℐ} µ̲ᵢ` and threshold value
`ν⋆ ≥ t̄ᵢ⋆` is optimal in (MDP).

**Formalization Note.** Agents form a finite type `ι` with at least two elements (`I ≥ 2`);
types are vectors `t : ι → ℝ`; `tlo i = t̲ᵢ`, `thi i = t̄ᵢ`, `c i = cᵢ`, with the standing
assumptions `0 ≤ t̲ᵢ < t̄ᵢ` and `cᵢ > 0` of §2 (p.5). `mlo i = µ̲ᵢ`, `mhi i = µ̄ᵢ`, with the standing assumption `t̲ᵢ < µ̲ᵢ < µ̄ᵢ < t̄ᵢ` of §4 (p.14). `i⋆ ∈ argmax µ̲` is `∀ i, µ̲ᵢ ≤ µ̲ᵢ⋆` (ties allowed). The mechanism is any
measurable favored-agent mechanism of type (i) or type (ii) with any choice of the case-(ii)
winner among the maximizers of `tᵢ − cᵢ`. -/
theorem theorem_3 {ι : Type*} [Fintype ι] [DecidableEq ι] (hI : 2 ≤ Fintype.card ι)
    (tlo thi c : ι → ℝ) (htlo : ∀ i, 0 ≤ tlo i) (htt : ∀ i, tlo i < thi i) (hc : ∀ i, 0 < c i)
    (mlo mhi : ι → ℝ) (hμ : ∀ i, tlo i < mlo i ∧ mlo i < mhi i ∧ mhi i < thi i)
    (istar : ι) (hmax : ∀ i, mlo i ≤ mlo istar) (ν : ℝ) (hν : thi istar ≤ ν)
    (p q : ι → (ι → ℝ) → ℝ) (hmeas : ∀ i, Measurable (p i) ∧ Measurable (q i))
    (hfa : IsFavoredAgent tlo thi c istar ν p q) :
    IsOptimal tlo thi (markovSet tlo thi mlo mhi) c p q := by sorry

end DRAllocCV
