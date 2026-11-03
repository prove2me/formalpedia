-- Prove2me | Theorems.Thm_DRAllocCV_lemma_3
-- name    : DRAllocCV.lemma_3
-- status  : Open
-- author  : @iris
-- created : 2026-11-03T05:13:41.640779+00:00
-- url     : https://prove2.me/theorems/bcb2f251-528f-4bd3-8873-d1867ae69824
-- title:
--   Lemma 3 — every type profile has positive mass under a two-point distribution in $\mathcal P$
-- statement:
--   A principal allocates one good among $I\ge2$ agents $i\in\mathcal I$. Agent $i$ has a type $t_i\in\mathcal T_i=[\underline t_i,\overline t_i]$ with $0\le\underline t_i<\overline t_i$, and inspecting agent $i$ costs $c_i>0$. Write $\mathcal T=\prod_i\mathcal T_i$ and $\mathcal X$ for the feasible mechanisms of (MDP). Let $\mathcal P=\{\mathbb P\in\mathcal P_0(\mathcal T):\mathbb E_{\mathbb P}[\tilde t_i]\in[\underline\mu_i,\overline\mu_i]\ \forall i\}$ be a Markov ambiguity set (5) with $\underline t_i<\underline\mu_i<\overline\mu_i<\overline t_i$ for all $i$. Assume $\arg\max_i\underline\mu_i=\{i^\star\}$ is a singleton.
--
--   Then for every type profile $t\in\mathcal T$ there are a scenario $\hat t\in\mathcal T$ with $\max_{i\ne i^\star}\hat t_i<\underline\mu_{i^\star}$ and a discrete distribution $\mathbb P\in\mathcal P$ such that
--
--   1. $\mathbb E_{\mathbb P}[\tilde t_i]=\underline\mu_i$ for all $i\in\mathcal I$;
--   2. $\mathbb P(\tilde t\in\{t,\hat t\})=1$;
--   3. $\mathbb P(\tilde t=t)>0$.
--
--   The lemma supplies condition (i) of Proposition 1 in the proof of Lemma 4.
--
--   Differences from the source:
--   - encoding: agents I = {1,…,I} with I ≥ 2 → a finite type ι with 2 ≤ Fintype.card ι; reason: relabelling of the agents; same instances
--   - encoding: distributions P ∈ 𝒫₀(𝒯) → probability measures P on ℝ^ι with P(𝒯ᶜ) = 0; reason: 𝒯 is closed, so these are exactly the Borel probability distributions on 𝒯
--   - encoding: arg max_i µ̲ᵢ = {i⋆} is a singleton → µ̲ᵢ < µ̲ᵢ⋆ for all i ≠ i⋆; reason: equivalent
--   - encoding: max_{i≠i⋆} t̂ᵢ < µ̲ᵢ⋆; "a discrete distribution P" with P(t̃ ∈ {t, t̂}) = 1 → ∀ i ≠ i⋆, t̂ᵢ < µ̲ᵢ⋆; P ∈ markovSet with P({t, t̂}ᶜ) = 0; reason: equivalent for I ≥ 2; discreteness follows from (ii)
-- source:
--   Bayrak, Koçyiğit, Kuhn, Pınar, Distributionally Robust Optimal Allocation with Costly Verification, arXiv:2211.15122v3, §4, p.15, Lemma 3

import Mathlib
import Definitions.Def_DRAllocCV_markovSet

open MeasureTheory

namespace DRAllocCV

/-- **Lemma 3** (Bayrak, Koçyiğit, Kuhn, Pınar, *Distributionally Robust Optimal Allocation with Costly Verification*, arXiv:2211.15122v3, §4, p.15). If `𝒫` is a Markov ambiguity set of the form (5) and
`argmax_{i ∈ ℐ} µ̲ᵢ = {i⋆}` is a singleton, then for any type profile `t ∈ 𝒯` there exist a
scenario `t̂ ∈ 𝒯` with `max_{i ≠ i⋆} t̂ᵢ < µ̲ᵢ⋆` and a discrete distribution `ℙ ∈ 𝒫` such that
(i) `𝔼_ℙ[t̃ᵢ] = µ̲ᵢ` for all `i ∈ ℐ`, (ii) `ℙ(t̃ ∈ {t, t̂}) = 1`, and (iii) `ℙ(t̃ = t) > 0`.

**Formalization Note.** Agents form a finite type `ι` with at least two elements (`I ≥ 2`);
types are vectors `t : ι → ℝ`; `tlo i = t̲ᵢ`, `thi i = t̄ᵢ`, `c i = cᵢ`, with the standing
assumptions `0 ≤ t̲ᵢ < t̄ᵢ` and `cᵢ > 0` of §2 (p.5). `mlo i = µ̲ᵢ`, `mhi i = µ̄ᵢ`, with the standing assumption `t̲ᵢ < µ̲ᵢ < µ̄ᵢ < t̄ᵢ` of §4 (p.14). The singleton hypothesis is `µ̲ᵢ < µ̲ᵢ⋆` for all `i ≠ i⋆`;
`max_{i ≠ i⋆} t̂ᵢ < µ̲ᵢ⋆` is `∀ i ≠ i⋆, t̂ᵢ < µ̲ᵢ⋆`. "Discrete" is implied by (ii), stated as
`ℙ({t, t̂}ᶜ) = 0`. -/
theorem lemma_3 {ι : Type*} [Fintype ι] [DecidableEq ι] (hI : 2 ≤ Fintype.card ι)
    (tlo thi c : ι → ℝ) (htlo : ∀ i, 0 ≤ tlo i) (htt : ∀ i, tlo i < thi i) (hc : ∀ i, 0 < c i)
    (mlo mhi : ι → ℝ) (hμ : ∀ i, tlo i < mlo i ∧ mlo i < mhi i ∧ mhi i < thi i)
    (istar : ι) (hsingle : ∀ i, i ≠ istar → mlo i < mlo istar)
    (t : ι → ℝ) (ht : t ∈ typeSpace tlo thi) :
    ∃ that ∈ typeSpace tlo thi, (∀ i, i ≠ istar → that i < mlo istar) ∧
      ∃ P ∈ markovSet tlo thi mlo mhi, (∀ i, ∫ s, s i ∂P = mlo i) ∧
        P ({t, that} : Set (ι → ℝ))ᶜ = 0 ∧ 0 < P {t} := by sorry

end DRAllocCV
