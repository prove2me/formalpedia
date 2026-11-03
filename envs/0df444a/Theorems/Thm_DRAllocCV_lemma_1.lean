-- Prove2me | Theorems.Thm_DRAllocCV_lemma_1
-- name    : DRAllocCV.lemma_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-03T05:14:18.985228+00:00
-- url     : https://prove2.me/theorems/02c68fb9-226a-4034-a338-17c23da29d56
-- title:
--   Lemma 1 — consequences of (IC) and (FC) along unilateral deviations
-- statement:
--   A principal allocates one good among $I\ge2$ agents $i\in\mathcal I$. Agent $i$ has a type $t_i\in\mathcal T_i=[\underline t_i,\overline t_i]$ with $0\le\underline t_i<\overline t_i$, and inspecting agent $i$ costs $c_i>0$. Write $\mathcal T=\prod_i\mathcal T_i$ and $\mathcal X$ for the feasible mechanisms of (MDP).
--
--   Let $(p,q)\in\mathcal X$, $i\in\mathcal I$ and $t\in\mathcal T$. A scenario $(t'_i,t_{-i})$ with $t'_i\in\mathcal T_i$ is called $i$-unilaterally reachable from $t$.
--
--   1. If $p_i(t)-q_i(t)=1$, then $p_i(t'_i,t_{-i})=1$ for all $t'_i\in\mathcal T_i$: if agent $i$ gets the good without inspection in $t$, he gets it in every $i$-unilaterally reachable scenario.
--   2. If $p_i(t)=0$, then $p_i(t'_i,t_{-i})=q_i(t'_i,t_{-i})$ for all $t'_i\in\mathcal T_i$: if agent $i$ does not get the good in $t$, he is inspected whenever he wins in an $i$-unilaterally reachable scenario.
--
--   These two facts are the non-local consequences of (IC) that drive the spatial induction behind Proposition 1 and Lemma 4.
--
--   Differences from the source:
--   - encoding: agents I = {1,…,I} with I ≥ 2 → a finite type ι with 2 ≤ Fintype.card ι; reason: relabelling of the agents; same instances
--   - encoding: mechanisms with p_i, q_i ∈ L(𝒯,[0,1]) (bounded Borel functions on 𝒯) → p q : ι → (ι → ℝ) → ℝ, Borel measurable on ℝ^ι, with [0,1] bounds required only on 𝒯; reason: every Borel function on the closed box 𝒯 extends to a Borel function on ℝ^ι; all notions depend only on the values on 𝒯
--   - encoding: the scenario (t′ᵢ, t₋ᵢ) → Function.update t i t′ᵢ; reason: same vector
-- source:
--   Bayrak, Koçyiğit, Kuhn, Pınar, Distributionally Robust Optimal Allocation with Costly Verification, arXiv:2211.15122v3, §2, p.9, Lemma 1

import Mathlib
import Definitions.Def_DRAllocCV_Feasible

open MeasureTheory

namespace DRAllocCV

/-- **Lemma 1** (Bayrak, Koçyiğit, Kuhn, Pınar, *Distributionally Robust Optimal Allocation with Costly Verification*, arXiv:2211.15122v3, §2, p.9). For any `(p, q) ∈ 𝒳`, `i ∈ ℐ` and `t ∈ 𝒯`:

1. if `pᵢ(t) − qᵢ(t) = 1`, then `pᵢ(t′ᵢ, t₋ᵢ) = 1` for all `t′ᵢ ∈ 𝒯ᵢ`;
2. if `pᵢ(t) = 0`, then `pᵢ(t′ᵢ, t₋ᵢ) = qᵢ(t′ᵢ, t₋ᵢ)` for all `t′ᵢ ∈ 𝒯ᵢ`.

**Formalization Note.** Agents form a finite type `ι` with at least two elements (`I ≥ 2`);
types are vectors `t : ι → ℝ`; `tlo i = t̲ᵢ`, `thi i = t̄ᵢ`, `c i = cᵢ`, with the standing
assumptions `0 ≤ t̲ᵢ < t̄ᵢ` and `cᵢ > 0` of §2 (p.5). The `i`-unilaterally reachable scenario `(t′ᵢ, t₋ᵢ)` is `Function.update t i t′ᵢ`. -/
theorem lemma_1 {ι : Type*} [Fintype ι] [DecidableEq ι] (hI : 2 ≤ Fintype.card ι)
    (tlo thi c : ι → ℝ) (htlo : ∀ i, 0 ≤ tlo i) (htt : ∀ i, tlo i < thi i) (hc : ∀ i, 0 < c i)
    (p q : ι → (ι → ℝ) → ℝ) (hX : Feasible tlo thi p q) (i : ι) (t : ι → ℝ)
    (ht : t ∈ typeSpace tlo thi) :
    (p i t - q i t = 1 → ∀ s ∈ Set.Icc (tlo i) (thi i), p i (Function.update t i s) = 1) ∧
    (p i t = 0 → ∀ s ∈ Set.Icc (tlo i) (thi i),
      p i (Function.update t i s) = q i (Function.update t i s)) := by sorry

end DRAllocCV
