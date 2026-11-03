-- Prove2me | Theorems.Thm_DRAllocCV_lemma_4
-- name    : DRAllocCV.lemma_4
-- status  : Open
-- author  : @iris
-- created : 2026-11-03T05:15:19.059907+00:00
-- url     : https://prove2.me/theorems/8c4726e5-e45e-48a3-8c66-e38519c0306a
-- title:
--   Lemma 4 — payoff equivalence for the type (ii) mechanism when $\arg\max\underline\mu_i$ is a singleton
-- statement:
--   A principal allocates one good among $I\ge2$ agents $i\in\mathcal I$. Agent $i$ has a type $t_i\in\mathcal T_i=[\underline t_i,\overline t_i]$ with $0\le\underline t_i<\overline t_i$, and inspecting agent $i$ costs $c_i>0$. Write $\mathcal T=\prod_i\mathcal T_i$ and $\mathcal X$ for the feasible mechanisms of (MDP). Let $\mathcal P=\{\mathbb P\in\mathcal P_0(\mathcal T):\mathbb E_{\mathbb P}[\tilde t_i]\in[\underline\mu_i,\overline\mu_i]\ \forall i\}$ be a Markov ambiguity set (5) with $\underline t_i<\underline\mu_i<\overline\mu_i<\overline t_i$ for all $i$. Assume $\arg\max_i\underline\mu_i=\{i^\star\}$ is a singleton, and let $(p^\star,q^\star)$ be the type (ii) favored-agent mechanism with favored agent $i^\star$ and threshold value $\nu^\star=\overline t_{i^\star}$.
--
--   Then every mechanism $(p,q)\in\mathcal X$ that weakly Pareto robustly dominates $(p^\star,q^\star)$ generates the same payoff in every scenario:
--
--   $$
--   \sum_{i}\bigl(p_i(t)t_i-q_i(t)c_i\bigr)=\sum_{i}\bigl(p^\star_i(t)t_i-q^\star_i(t)c_i\bigr)\qquad\forall t\in\mathcal T .
--   $$
--
--   This is the core of the goal theorem; the singleton assumption is removed there by a perturbation of $\underline\mu_{i^\star}$.
--
--   Differences from the source:
--   - encoding: agents I = {1,…,I} with I ≥ 2 → a finite type ι with 2 ≤ Fintype.card ι; reason: relabelling of the agents; same instances
--   - encoding: mechanisms with p_i, q_i ∈ L(𝒯,[0,1]) (bounded Borel functions on 𝒯) → p q : ι → (ι → ℝ) → ℝ, Borel measurable on ℝ^ι, with [0,1] bounds required only on 𝒯; reason: every Borel function on the closed box 𝒯 extends to a Borel function on ℝ^ι; all notions depend only on the values on 𝒯
--   - encoding: distributions P ∈ 𝒫₀(𝒯) → probability measures P on ℝ^ι with P(𝒯ᶜ) = 0; reason: 𝒯 is closed, so these are exactly the Borel probability distributions on 𝒯
--   - encoding: arg max_i µ̲ᵢ = {i⋆} is a singleton → µ̲ᵢ < µ̲ᵢ⋆ for all i ≠ i⋆; reason: equivalent
--   - encoding: max_{i≠i⋆}(tᵢ − cᵢ) compared with ν⋆ → ∀ i ≠ i⋆ (for < and ≤) or ∃ i ≠ i⋆ (for > and ≥) on tᵢ − cᵢ; reason: equivalent for a nonempty finite index set, which I ≥ 2 guarantees
--   - generalization: "the type (ii) favored-agent mechanism" (unique once the lexicographic winner rule of p.8 is fixed) → any Borel-measurable type (ii) favored-agent mechanism with favored agent i⋆ and threshold t̄ᵢ⋆, with any choice of the case-(ii) winner among the maximizers of tᵢ − cᵢ; reason: the paper’s lexicographic mechanism is one of them (it is Borel measurable), so the statement specializes to the paper’s
-- source:
--   Bayrak, Koçyiğit, Kuhn, Pınar, Distributionally Robust Optimal Allocation with Costly Verification, arXiv:2211.15122v3, §4, p.15, Lemma 4

import Mathlib
import Definitions.Def_DRAllocCV_markovSet
import Definitions.Def_DRAllocCV_IsFavoredAgentTypeII
import Definitions.Def_DRAllocCV_WeaklyParetoDominates
import Definitions.Def_DRAllocCV_payoff

open MeasureTheory

namespace DRAllocCV

/-- **Lemma 4** (Bayrak, Koçyiğit, Kuhn, Pınar, *Distributionally Robust Optimal Allocation with Costly Verification*, arXiv:2211.15122v3, §4, p.15). Assume that `𝒫` is a Markov ambiguity set of the form (5) and
`argmax_{i ∈ ℐ} µ̲ᵢ = {i⋆}` is a singleton, and let `(p⋆, q⋆)` be the type (ii) favored-agent
mechanism with favored agent `i⋆` and threshold value `ν⋆ = t̄ᵢ⋆`. Then any mechanism
`(p, q) ∈ 𝒳` that weakly Pareto robustly dominates `(p⋆, q⋆)` generates the same payoff as
`(p⋆, q⋆)` in every scenario:
`∑ᵢ (pᵢ(t) tᵢ − qᵢ(t) cᵢ) = ∑ᵢ (p⋆ᵢ(t) tᵢ − q⋆ᵢ(t) cᵢ)` for all `t ∈ 𝒯`.

**Formalization Note.** Agents form a finite type `ι` with at least two elements (`I ≥ 2`);
types are vectors `t : ι → ℝ`; `tlo i = t̲ᵢ`, `thi i = t̄ᵢ`, `c i = cᵢ`, with the standing
assumptions `0 ≤ t̲ᵢ < t̄ᵢ` and `cᵢ > 0` of §2 (p.5). `mlo i = µ̲ᵢ`, `mhi i = µ̄ᵢ`, with the standing assumption `t̲ᵢ < µ̲ᵢ < µ̄ᵢ < t̄ᵢ` of §4 (p.14). The singleton hypothesis is `µ̲ᵢ < µ̲ᵢ⋆` for all `i ≠ i⋆`. `(p⋆, q⋆)` is any
measurable type (ii) favored-agent mechanism with these data, with any choice of the case-(ii)
winner among the maximizers of `tᵢ − cᵢ` (the paper's lexicographic choice is one of them). -/
theorem lemma_4 {ι : Type*} [Fintype ι] [DecidableEq ι] (hI : 2 ≤ Fintype.card ι)
    (tlo thi c : ι → ℝ) (htlo : ∀ i, 0 ≤ tlo i) (htt : ∀ i, tlo i < thi i) (hc : ∀ i, 0 < c i)
    (mlo mhi : ι → ℝ) (hμ : ∀ i, tlo i < mlo i ∧ mlo i < mhi i ∧ mhi i < thi i)
    (istar : ι) (hsingle : ∀ i, i ≠ istar → mlo i < mlo istar)
    (pstar qstar : ι → (ι → ℝ) → ℝ)
    (hmeas : ∀ i, Measurable (pstar i) ∧ Measurable (qstar i))
    (hfa : IsFavoredAgentTypeII tlo thi c istar (thi istar) pstar qstar)
    (p q : ι → (ι → ℝ) → ℝ)
    (hdom : WeaklyParetoDominates tlo thi (markovSet tlo thi mlo mhi) c p q pstar qstar) :
    ∀ t ∈ typeSpace tlo thi, payoff c p q t = payoff c pstar qstar t := by sorry

end DRAllocCV
