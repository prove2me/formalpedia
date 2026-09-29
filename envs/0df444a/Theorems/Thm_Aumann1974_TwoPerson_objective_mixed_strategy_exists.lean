-- Prove2me | Theorems.Thm_Aumann1974_TwoPerson_objective_mixed_strategy_exists
-- name    : Aumann1974.TwoPerson.objective_mixed_strategy_exists
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-27T10:41:02.794363+00:00
-- url     : https://prove2.me/theorems/e391a75e-beff-423f-8588-149f9d25e7b1
-- title:
--   Lemma 4.1 — every distribution on $S_i$ is realised by an objective mixed strategy
-- statement:
--   Let $(\Omega,\mathcal B,(\mathcal J_i),(p_i))$ be a randomizing structure for a finite set $N$ of players satisfying Assumption II. Let $i\in N$, let $S_i$ be a finite set, and let $\sigma_i$ be a **distribution** on $S_i$ (a real function with nonnegative values summing to $1$). Then player $i$ has a strategy $s_i : \Omega \to S_i$ that is **mixed** (every level set $\{s_i = a\}$ is $i$-secret) and **objective** (every level set has the same probability under all $p_j$), with
--   $$p\{s_i = a\} = \sigma_i(a)\qquad\text{for all } a \in S_i,$$
--   where $p\{s_i=a\}$ is the common value of the subjective probabilities $p_j\{s_i=a\}$, $j \in N$.
--
--   In words: every classical mixed strategy of non-cooperative game theory appears in Aumann's model as an objective mixed strategy. This is the step that embeds the classical theory in the subjective model and is used both for Proposition 4.3 and in the proof of Proposition 5.1.
--
--   **Formalization Note** The paper uses the letter $s_i$ both for the strategy and for a pure strategy; here the pure strategy is $a$. Distributions are `AGT.IsLottery` from the definition `agt_games`. The conclusion states $p_j\{s_i=a\}=\sigma_i(a)$ for every player $j$ (which also makes the strategy objective) and lists objectivity explicitly.
-- source:
--   R. J. Aumann, Subjectivity and Correlation in Randomized Strategies, J. Math. Econ. 1 (1974) 67–96, https://doi.org/10.1016/0304-4068(74)90037-8, p. 77 (PDF p. 11), Lemma 4.1; proof p. 82 (PDF p. 16)

import Mathlib
import Definitions.Def_agt_games
import Definitions.Def_Aumann1974_TwoPerson_RandomizingStructure

namespace Aumann1974.TwoPerson

open MeasureTheory

/-- **Lemma 4.1** (Aumann 1974, *Subjectivity and Correlation in Randomized Strategies*,
J. Math. Econ. 1, p. 77, PDF p. 11): let `i ∈ N`, and let `σᵢ` be a distribution on `Sᵢ`. Then
`i` has an objective mixed strategy `sᵢ` such that for all `a ∈ Sᵢ`, `p{sᵢ = a} = σᵢ(a)`.

**Formalization Note.** A distribution on `Sᵢ` is `AGT.IsLottery` (nonnegative real weights
summing to `1`, the paper's definition on p. 77). The paper writes `sᵢ` both for the strategy and
for the pure strategy; here the pure strategy is `a`. `p{sᵢ = a}` is the common value of the
subjective probabilities of the objective event `{sᵢ = a}`, so the conclusion states
`pⱼ{sᵢ = a} = σᵢ(a)` for every player `j`. "Mixed" (`IsMixed`) implies "strategy of `i`".
Assumption II (the paper's standing assumption, p. 75) is a hypothesis; the players form a
finite type with decidable equality and `Sᵢ` is finite. -/
theorem objective_mixed_strategy_exists {ι Ω : Type*} [Fintype ι] [DecidableEq ι]
    {mΩ : MeasurableSpace Ω} {S : ι → Type*} [∀ i, Fintype (S i)]
    (R : RandomizingStructure ι Ω mΩ) (hII : AssumptionII R)
    (i : ι) (σ : S i → ℝ) (hσ : AGT.IsLottery σ) :
    ∃ s : Ω → S i, IsMixed R i s ∧ IsObjectiveStrategy R s ∧
      ∀ (a : S i) (j : ι), R.p j {ω | s ω = a} = ENNReal.ofReal (σ a) := by sorry

end Aumann1974.TwoPerson
