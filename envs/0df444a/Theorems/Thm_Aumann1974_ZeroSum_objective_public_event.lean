-- Prove2me | Theorems.Thm_Aumann1974_ZeroSum_objective_public_event
-- name    : Aumann1974.ZeroSum.objective_public_event
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-27T11:06:43.499826+00:00
-- url     : https://prove2.me/theorems/b126ae8d-27ac-4541-9b0e-a8b3ac3551ed
-- title:
--   Lemma 4.4 — with a public roulette, an objective public event of any probability $\alpha$, independent of a given event
-- statement:
--   Let $(\Omega,\mathcal B,(\mathcal J_i),(p_i))$ be a randomizing structure for a finite set $N$ of players satisfying Assumption II, and assume that there is a **public roulette**: a sub-$\sigma$-field $\mathcal R\subseteq\bigcap_{i\in N}\mathcal J_i$ on which every $p_j$ is non-atomic. Then for every event $B\in\mathcal B$ and every $\alpha\in[0,1]$ there is a **public** event $A$ (one in every $\mathcal J_i$) such that
--   $$p_j(A)=\alpha\quad\text{and}\quad p_j(A\cap B)=p_j(A)\,p_j(B)\qquad\text{for every player } j.$$
--
--   A public roulette is a correlating device on which all players can peg their choices. The lemma is what the Remark after Proposition 6.1 uses to scale a public event $C$ to a public event $\theta C$ with $p_i(\theta C)=\theta\,p_i(C)$ for both players.
--
--   **Formalization Note** Assumption II is carried as the paper's standing assumption although the proof (Lemma 7.1 applied to the public roulette) does not use it. Public events are also required to lie in $\mathcal B$. Footnote 17 of the paper refers to this lemma as "Proposition 4.4" (misprint).
-- source:
--   R. J. Aumann, Subjectivity and Correlation in Randomized Strategies, J. Math. Econ. 1 (1974) 67–96, https://doi.org/10.1016/0304-4068(74)90037-8, p. 77 (PDF p. 11), Lemma 4.4; public events and public roulette defined p. 77; proof via Lemma 7.1, pp. 81–82 (PDF pp. 15–16)

import Mathlib
import Definitions.Def_Aumann1974_ZeroSum_RandomizingStructure

namespace Aumann1974.ZeroSum

open MeasureTheory

/-- **Lemma 4.4** (Aumann 1974, *Subjectivity and Correlation in Randomized Strategies*,
J. Math. Econ. 1, p. 77, PDF p. 11): assume that there is a public roulette. Then for any event
`B`, and any `α` between `0` and `1`, there is an objective public event with probability `α` that
is independent of `B`.

**Formalization Note.** A public roulette is a σ-algebra `m ≤ ℬ` of public events (events in
every `𝒥ᵢ`) on which every `pⱼ` is non-atomic (`IsPublicRoulette`). The players form a finite
type. `B` is any `ℬ`-measurable event; "objective with probability `α`" and "independent of `B`"
are required for every player. Assumption II (standing assumption, p. 75) is carried as a
hypothesis although the proof (Lemma 7.1 applied to the public roulette) does not use it.
Footnote 17 (p. 80) calls this result "Proposition 4.4" (misprint). -/
theorem objective_public_event {ι Ω : Type*} [Fintype ι] {mΩ : MeasurableSpace Ω}
    (R : RandomizingStructure ι Ω mΩ) (hII : AssumptionII R)
    (hpub : ∃ m : MeasurableSpace Ω, IsPublicRoulette R m)
    (B : Set Ω) (hB : MeasurableSet[mΩ] B)
    (α : ℝ) (hα0 : 0 ≤ α) (hα1 : α ≤ 1) :
    ∃ A : Set Ω, IsPublic R A ∧ IsObjective R A ∧
      (∀ j, R.p j A = ENNReal.ofReal α) ∧ IsIndependentOf R A B := by sorry

end Aumann1974.ZeroSum
