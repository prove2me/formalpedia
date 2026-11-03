-- Prove2me | Theorems.Thm_DRAllocCV_theorem_4
-- name    : DRAllocCV.theorem_4
-- status  : Open
-- author  : @iris
-- created : 2026-11-03T05:17:00.846771+00:00
-- url     : https://prove2.me/theorems/516723bc-1471-4d67-80c7-92b183c8c50e
-- title:
--   Theorem 4 — under Markov ambiguity the type (ii) favored-agent mechanism with $\nu^\star=\overline t_{i^\star}$ is Pareto robustly optimal
-- statement:
--   A principal allocates one good among $I\ge2$ agents $i\in\mathcal I$. Agent $i$ has a type $t_i\in\mathcal T_i=[\underline t_i,\overline t_i]$ with $0\le\underline t_i<\overline t_i$, and inspecting agent $i$ costs $c_i>0$. Write $\mathcal T=\prod_i\mathcal T_i$ and $\mathcal X$ for the feasible mechanisms of (MDP). Let $\mathcal P=\{\mathbb P\in\mathcal P_0(\mathcal T):\mathbb E_{\mathbb P}[\tilde t_i]\in[\underline\mu_i,\overline\mu_i]\ \forall i\}$ be a Markov ambiguity set (5) with $\underline t_i<\underline\mu_i<\overline\mu_i<\overline t_i$ for all $i$.
--
--   Let $(p^\star,q^\star)$ be a type (ii) favored-agent mechanism with favored agent and threshold value
--
--   $$
--   i^\star\in\arg\max_{i\in\mathcal I}\underline\mu_i,\qquad \nu^\star=\overline t_{i^\star}.
--   $$
--
--   Then $(p^\star,q^\star)$ is **Pareto robustly optimal** in (MDP): it is optimal (its worst-case expected payoff is $z^\star=\max_i\underline\mu_i$), and no feasible mechanism $(p,q)\in\mathcal X$ achieves an expected payoff at least as large under every $\mathbb P\in\mathcal P$ and strictly larger under some $\mathbb P\in\mathcal P$.
--
--   The argmax need not be a singleton. Among the many optimal favored-agent mechanisms of Theorem 3, this one cannot be improved on any distribution of the ambiguity set; competitors range over all feasible mechanisms, including randomized ones that are not favored-agent mechanisms.
--
--   Differences from the source:
--   - encoding: agents I = {1,…,I} with I ≥ 2 → a finite type ι with 2 ≤ Fintype.card ι; reason: relabelling of the agents; same instances
--   - encoding: mechanisms with p_i, q_i ∈ L(𝒯,[0,1]) (bounded Borel functions on 𝒯) → p q : ι → (ι → ℝ) → ℝ, Borel measurable on ℝ^ι, with [0,1] bounds required only on 𝒯; reason: every Borel function on the closed box 𝒯 extends to a Borel function on ℝ^ι; all notions depend only on the values on 𝒯
--   - encoding: distributions P ∈ 𝒫₀(𝒯) → probability measures P on ℝ^ι with P(𝒯ᶜ) = 0; reason: 𝒯 is closed, so these are exactly the Borel probability distributions on 𝒯
--   - encoding: optimal: worst-case expected payoff inf_P E_P equals z⋆ = sup inf → IsOptimal: feasible, and every lower bound of a competitor’s expected payoffs over 𝒫 is a lower bound of its own; reason: equivalent comparison of the infima in the extended reals, without a real ⨅ that would be junk on empty or unbounded sets
--   - encoding: i⋆ ∈ arg max_i µ̲ᵢ → ∀ i, µ̲ᵢ ≤ µ̲ᵢ⋆; reason: equivalent
--   - encoding: max_{i≠i⋆}(tᵢ − cᵢ) compared with ν⋆ → ∀ i ≠ i⋆ (for < and ≤) or ∃ i ≠ i⋆ (for > and ≥) on tᵢ − cᵢ; reason: equivalent for a nonempty finite index set, which I ≥ 2 guarantees
--   - generalization: "any type (ii) favored-agent mechanism" with the lexicographic case-(ii) winner fixed on p.8 → any Borel-measurable type (ii) favored-agent mechanism with favored agent i⋆ and threshold t̄ᵢ⋆, with any choice of the case-(ii) winner among the maximizers of tᵢ − cᵢ; reason: the paper’s lexicographic mechanism is one of them (it is Borel measurable), so the statement specializes to the paper’s
-- source:
--   Bayrak, Koçyiğit, Kuhn, Pınar, Distributionally Robust Optimal Allocation with Costly Verification, arXiv:2211.15122v3, §4, p.17, Theorem 4

import Mathlib
import Definitions.Def_DRAllocCV_markovSet
import Definitions.Def_DRAllocCV_IsFavoredAgentTypeII
import Definitions.Def_DRAllocCV_IsParetoRobustlyOptimal

open MeasureTheory

namespace DRAllocCV

/-- **Theorem 4** (Bayrak, Koçyiğit, Kuhn, Pınar, *Distributionally Robust Optimal Allocation with Costly Verification*, arXiv:2211.15122v3, §4, p.17). If `𝒫` is a Markov ambiguity set of the form (5), then any
type (ii) favored-agent mechanism `(p⋆, q⋆)` with favored agent `i⋆ ∈ argmax_{i ∈ ℐ} µ̲ᵢ` and
threshold value `ν⋆ = t̄ᵢ⋆` is Pareto robustly optimal in (MDP): it is optimal, and no feasible
mechanism Pareto robustly dominates it.

**Formalization Note.** Agents form a finite type `ι` with at least two elements (`I ≥ 2`);
types are vectors `t : ι → ℝ`; `tlo i = t̲ᵢ`, `thi i = t̄ᵢ`, `c i = cᵢ`, with the standing
assumptions `0 ≤ t̲ᵢ < t̄ᵢ` and `cᵢ > 0` of §2 (p.5). `mlo i = µ̲ᵢ`, `mhi i = µ̄ᵢ`, with the standing assumption `t̲ᵢ < µ̲ᵢ < µ̄ᵢ < t̄ᵢ` of §4 (p.14). `i⋆ ∈ argmax µ̲` is `∀ i, µ̲ᵢ ≤ µ̲ᵢ⋆`; ties in the argmax are allowed (the
argmax need not be a singleton). `(p⋆, q⋆)` is any measurable type (ii) favored-agent mechanism
with these data, with any choice of the case-(ii) winner among the maximizers of `tᵢ − cᵢ` (the
paper's lexicographic choice is one of them). Competitors range over all of `𝒳`; distributions
over all Borel probability measures on `𝒯` in the Markov set. -/
theorem theorem_4 {ι : Type*} [Fintype ι] [DecidableEq ι] (hI : 2 ≤ Fintype.card ι)
    (tlo thi c : ι → ℝ) (htlo : ∀ i, 0 ≤ tlo i) (htt : ∀ i, tlo i < thi i) (hc : ∀ i, 0 < c i)
    (mlo mhi : ι → ℝ) (hμ : ∀ i, tlo i < mlo i ∧ mlo i < mhi i ∧ mhi i < thi i)
    (istar : ι) (hmax : ∀ i, mlo i ≤ mlo istar)
    (pstar qstar : ι → (ι → ℝ) → ℝ)
    (hmeas : ∀ i, Measurable (pstar i) ∧ Measurable (qstar i))
    (hfa : IsFavoredAgentTypeII tlo thi c istar (thi istar) pstar qstar) :
    IsParetoRobustlyOptimal tlo thi (markovSet tlo thi mlo mhi) c pstar qstar := by sorry

end DRAllocCV
