-- Prove2me | Theorems.Thm_DRAllocCV_corollary_1
-- name    : DRAllocCV.corollary_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-03T05:15:29.946224+00:00
-- url     : https://prove2.me/theorems/b793fbb2-0201-41db-8540-3e1fa132ed80
-- title:
--   Corollary 1 — payoff equivalence
-- statement:
--   A principal allocates one good among $I\ge2$ agents $i\in\mathcal I$. Agent $i$ has a type $t_i\in\mathcal T_i=[\underline t_i,\overline t_i]$ with $0\le\underline t_i<\overline t_i$, and inspecting agent $i$ costs $c_i>0$. Write $\mathcal T=\prod_i\mathcal T_i$ and $\mathcal X$ for the feasible mechanisms of (MDP). Let $\mathcal P\subseteq\mathcal P_0(\mathcal T)$ be any ambiguity set.
--
--   Let $(p^\star,q^\star)\in\mathcal X$ be optimal in (MDP), and let $S_1,\dots,S_m$ be a partition of $\mathcal T$ such that for every $k\in\{1,\dots,m\}$ and every scenario $t\in S_k$:
--
--   1. there is $\mathbb P\in\mathcal P\cap\mathcal P_0\bigl(\bigcup_{l=1}^kS_l\bigr)$ with $\mathbb P(\tilde t=t)>0$;
--   2. $(p^\star,q^\star)$ solves the scenario problem $\mathrm{SP}_k(t)$:
--   $$
--   \max_{(p,q)\in\mathcal X}\sum_i\bigl(p_i(t)t_i-q_i(t)c_i\bigr)\ \ \text{s.t.}\ \ \sum_i\bigl(p_i(t')t'_i-q_i(t')c_i\bigr)=\sum_i\bigl(p^\star_i(t')t'_i-q^\star_i(t')c_i\bigr)\ \ \forall t'\in\textstyle\bigcup_{l=1}^{k-1}S_l .
--   $$
--
--   If a mechanism $(p,q)\in\mathcal X$ weakly Pareto robustly dominates $(p^\star,q^\star)$, then it generates the same payoff in every scenario:
--
--   $$
--   \sum_{i}\bigl(p_i(t)t_i-q_i(t)c_i\bigr)=\sum_{i}\bigl(p^\star_i(t)t_i-q^\star_i(t)c_i\bigr)\qquad\forall t\in\mathcal T .
--   $$
--
--   This is the form in which Proposition 1 is used in the proof of Lemma 4.
--
--   Differences from the source:
--   - encoding: agents I = {1,…,I} with I ≥ 2 → a finite type ι with 2 ≤ Fintype.card ι; reason: relabelling of the agents; same instances
--   - encoding: mechanisms with p_i, q_i ∈ L(𝒯,[0,1]) (bounded Borel functions on 𝒯) → p q : ι → (ι → ℝ) → ℝ, Borel measurable on ℝ^ι, with [0,1] bounds required only on 𝒯; reason: every Borel function on the closed box 𝒯 extends to a Borel function on ℝ^ι; all notions depend only on the values on 𝒯
--   - encoding: an ambiguity set 𝒫 ⊆ 𝒫₀(𝒯) → Pset : Set (Measure (ι → ℝ)) whose members are probability measures with P(𝒯ᶜ) = 0; reason: same objects (see the 𝒫₀(𝒯) encoding)
--   - encoding: optimal: worst-case expected payoff inf_P E_P equals z⋆ = sup inf → IsOptimal: feasible, and every lower bound of a competitor’s expected payoffs over 𝒫 is a lower bound of its own; reason: equivalent comparison of the infima in the extended reals, without a real ⨅ that would be junk on empty or unbounded sets
--   - generalization: a partition S₁,…,S_m of 𝒯 with P ∈ 𝒫₀(∪_{l≤k} S_l), which needs Borel unions → any pairwise disjoint family S : Fin m → Set (ℝ^ι) covering 𝒯 (cells need not be measurable, empty cells allowed); condition (i) as P((∪_{l≤k} S_l)ᶜ) = 0 (outer measure) and P({t}) > 0; reason: a Borel partition of nonempty cells is a special case, for which P((∪ S_l)ᶜ) = 0 means P ∈ 𝒫₀(∪ S_l)
--   - encoding: (p⋆,q⋆) solves SP_k(t) → SolvesScenarioProblem: (p⋆,q⋆) is feasible and every feasible point of SP_k(t) has objective value at most that of (p⋆,q⋆); cells indexed by Fin m; reason: the definition of solving a maximization problem; Lean cell k is the paper’s S_{k+1}
-- source:
--   Bayrak, Koçyiğit, Kuhn, Pınar, Distributionally Robust Optimal Allocation with Costly Verification, arXiv:2211.15122v3, §2, p.10, Corollary 1 (Payoff Equivalence)

import Mathlib
import Definitions.Def_DRAllocCV_WeaklyParetoDominates
import Definitions.Def_DRAllocCV_IsOptimal
import Definitions.Def_DRAllocCV_SolvesScenarioProblem
import Definitions.Def_DRAllocCV_typeSpace

open MeasureTheory

namespace DRAllocCV

/-- **Corollary 1** (payoff equivalence, Bayrak, Koçyiğit, Kuhn, Pınar, *Distributionally Robust Optimal Allocation with Costly Verification*, arXiv:2211.15122v3, §2, p.10). Let `(p⋆, q⋆) ∈ 𝒳` be an optimal
mechanism satisfying conditions (i) and (ii) of Proposition 1 for a partition `S₁, …, S_m` of
`𝒯`. If a mechanism `(p, q) ∈ 𝒳` weakly Pareto robustly dominates `(p⋆, q⋆)`, then it generates
the same payoff as `(p⋆, q⋆)` in every scenario `t ∈ 𝒯`.

**Formalization Note.** Agents form a finite type `ι` with at least two elements (`I ≥ 2`);
types are vectors `t : ι → ℝ`; `tlo i = t̲ᵢ`, `thi i = t̄ᵢ`, `c i = cᵢ`, with the standing
assumptions `0 ≤ t̲ᵢ < t̄ᵢ` and `cᵢ > 0` of §2 (p.5). The ambiguity set `𝒫 ⊆ 𝒫₀(𝒯)` (`Pset`) is arbitrary: its elements are probability measures on
`ι → ℝ` with `ℙ(𝒯ᶜ) = 0`. The partition is a family `S : Fin m → Set (ι → ℝ)` of pairwise disjoint
sets with union `𝒯` (Lean's cell `k` is the paper's `S_{k+1}`; empty cells are allowed, which
changes nothing since they impose no condition and do not change the unions). Condition (i),
`ℙ ∈ 𝒫 ∩ 𝒫₀(⋃_{l=1}^k S_l)` with `ℙ(t̃ = t) > 0`, is `ℙ ∈ 𝒫`, `ℙ((⋃_{l ≤ k} S_l)ᶜ) = 0` and
`ℙ({t}) > 0`; the cells need not be measurable (the measure of a set is its outer measure). -/
theorem corollary_1 {ι : Type*} [Fintype ι] [DecidableEq ι] (hI : 2 ≤ Fintype.card ι)
    (tlo thi c : ι → ℝ) (htlo : ∀ i, 0 ≤ tlo i) (htt : ∀ i, tlo i < thi i) (hc : ∀ i, 0 < c i)
    (Pset : Set (Measure (ι → ℝ)))
    (hPset : ∀ P ∈ Pset, IsProbabilityMeasure P ∧ P (typeSpace tlo thi)ᶜ = 0)
    (pstar qstar : ι → (ι → ℝ) → ℝ) (hopt : IsOptimal tlo thi Pset c pstar qstar)
    {m : ℕ} (S : Fin m → Set (ι → ℝ)) (hdisj : Pairwise fun k l => Disjoint (S k) (S l))
    (hcover : ⋃ k, S k = typeSpace tlo thi)
    (hcond_i : ∀ k, ∀ t ∈ S k, ∃ P ∈ Pset, P (⋃ l, ⋃ (_ : l ≤ k), S l)ᶜ = 0 ∧ 0 < P {t})
    (hcond_ii : ∀ k, ∀ t ∈ S k, SolvesScenarioProblem tlo thi c S pstar qstar k t)
    (p q : ι → (ι → ℝ) → ℝ) (hdom : WeaklyParetoDominates tlo thi Pset c p q pstar qstar) :
    ∀ t ∈ typeSpace tlo thi, payoff c p q t = payoff c pstar qstar t := by sorry

end DRAllocCV
