-- Prove2me | Theorems.Thm_DRAllocCV_proposition_3
-- name    : DRAllocCV.proposition_3
-- status  : Open
-- author  : @iris
-- created : 2026-11-03T05:14:43.105736+00:00
-- url     : https://prove2.me/theorems/5b5594e5-6d20-4efc-bb96-898cfb2d48b9
-- title:
--   Proposition 3 — under Markov ambiguity (MDP) is solvable with $z^\star=\max_i\underline\mu_i$
-- statement:
--   A principal allocates one good among $I\ge2$ agents $i\in\mathcal I$. Agent $i$ has a type $t_i\in\mathcal T_i=[\underline t_i,\overline t_i]$ with $0\le\underline t_i<\overline t_i$, and inspecting agent $i$ costs $c_i>0$. Write $\mathcal T=\prod_i\mathcal T_i$ and $\mathcal X$ for the feasible mechanisms of (MDP). Let $\mathcal P=\{\mathbb P\in\mathcal P_0(\mathcal T):\mathbb E_{\mathbb P}[\tilde t_i]\in[\underline\mu_i,\overline\mu_i]\ \forall i\}$ be a Markov ambiguity set (5) with $\underline t_i<\underline\mu_i<\overline\mu_i<\overline t_i$ for all $i$.
--
--   Then problem (MDP) is solvable and its optimal value is
--
--   $$
--   z^\star=\max_{i\in\mathcal I}\underline\mu_i .
--   $$
--
--   Precisely: (a) every feasible mechanism has worst-case expected payoff $\inf_{\mathbb P\in\mathcal P}\mathbb E_{\mathbb P}[\cdot]$ at most $\max_i\underline\mu_i$, and (b) some feasible mechanism has expected payoff at least $\max_i\underline\mu_i$ under every $\mathbb P\in\mathcal P$.
--
--   Knowing the mean bounds raises the principal's guaranteed payoff from $\max_i\underline t_i$ (support information only, Proposition 2) to $\max_i\underline\mu_i$.
--
--   Differences from the source:
--   - encoding: agents I = {1,…,I} with I ≥ 2 → a finite type ι with 2 ≤ Fintype.card ι; reason: relabelling of the agents; same instances
--   - encoding: mechanisms with p_i, q_i ∈ L(𝒯,[0,1]) (bounded Borel functions on 𝒯) → p q : ι → (ι → ℝ) → ℝ, Borel measurable on ℝ^ι, with [0,1] bounds required only on 𝒯; reason: every Borel function on the closed box 𝒯 extends to a Borel function on ℝ^ι; all notions depend only on the values on 𝒯
--   - encoding: distributions P ∈ 𝒫₀(𝒯) → probability measures P on ℝ^ι with P(𝒯ᶜ) = 0; reason: 𝒯 is closed, so these are exactly the Borel probability distributions on 𝒯
--   - encoding: z⋆ = max_i µ̲ᵢ and solvability → (a) every lower bound z of a feasible mechanism’s expected payoffs over 𝒫 satisfies z ≤ max_i µ̲ᵢ (Finset.sup′); (b) some feasible mechanism has expected payoff ≥ max_i µ̲ᵢ under every P ∈ 𝒫; reason: 𝒫 is nonempty (δ at µ̲ belongs to it) and expected payoffs of feasible mechanisms are bounded below, so (a) is sup inf ≤ max µ̲ and (b) is attainment
-- source:
--   Bayrak, Koçyiğit, Kuhn, Pınar, Distributionally Robust Optimal Allocation with Costly Verification, arXiv:2211.15122v3, §4, p.14, Proposition 3

import Mathlib
import Definitions.Def_DRAllocCV_markovSet
import Definitions.Def_DRAllocCV_Feasible
import Definitions.Def_DRAllocCV_expectedPayoff

open MeasureTheory

namespace DRAllocCV

/-- **Proposition 3** (Bayrak, Koçyiğit, Kuhn, Pınar, *Distributionally Robust Optimal Allocation with Costly Verification*, arXiv:2211.15122v3, §4, p.14). If `𝒫` is a Markov ambiguity set of the form (5), then
problem (MDP) is solvable and `z⋆ = max_{i ∈ ℐ} µ̲ᵢ`.

The statement has two parts: (a) no feasible mechanism has a worst-case expected payoff above
`max_i µ̲ᵢ` (every lower bound `z` of its expected payoffs over `𝒫` satisfies `z ≤ max_i µ̲ᵢ`);
(b) some feasible mechanism attains it (its expected payoff is at least `max_i µ̲ᵢ` under every
`ℙ ∈ 𝒫`).

**Formalization Note.** Agents form a finite type `ι` with at least two elements (`I ≥ 2`);
types are vectors `t : ι → ℝ`; `tlo i = t̲ᵢ`, `thi i = t̄ᵢ`, `c i = cᵢ`, with the standing
assumptions `0 ≤ t̲ᵢ < t̄ᵢ` and `cᵢ > 0` of §2 (p.5). `mlo i = µ̲ᵢ`, `mhi i = µ̄ᵢ`, with the standing assumption `t̲ᵢ < µ̲ᵢ < µ̄ᵢ < t̄ᵢ` of §4 (p.14). The worst-case value is handled through lower bounds rather than a real
`⨅`, which would return junk on an unbounded or empty family. -/
theorem proposition_3 {ι : Type*} [Fintype ι] [DecidableEq ι] (hI : 2 ≤ Fintype.card ι)
    (tlo thi c : ι → ℝ) (htlo : ∀ i, 0 ≤ tlo i) (htt : ∀ i, tlo i < thi i) (hc : ∀ i, 0 < c i)
    (mlo mhi : ι → ℝ) (hμ : ∀ i, tlo i < mlo i ∧ mlo i < mhi i ∧ mhi i < thi i) :
    (∀ p q, Feasible tlo thi p q → ∀ z : ℝ,
        (∀ P ∈ markovSet tlo thi mlo mhi, z ≤ expectedPayoff P c p q) →
        z ≤ Finset.univ.sup' (Finset.univ_nonempty_iff.mpr (Fintype.card_pos_iff.mp (by omega)))
          mlo) ∧
    ∃ p q, Feasible tlo thi p q ∧ ∀ P ∈ markovSet tlo thi mlo mhi,
      Finset.univ.sup' (Finset.univ_nonempty_iff.mpr (Fintype.card_pos_iff.mp (by omega))) mlo ≤
        expectedPayoff P c p q := by sorry

end DRAllocCV
