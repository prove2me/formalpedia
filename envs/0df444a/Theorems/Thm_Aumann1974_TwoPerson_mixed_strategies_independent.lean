-- Prove2me | Theorems.Thm_Aumann1974_TwoPerson_mixed_strategies_independent
-- name    : Aumann1974.TwoPerson.mixed_strategies_independent
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-27T10:48:34.509219+00:00
-- url     : https://prove2.me/theorems/832b3596-241b-403f-bed7-657795dc4d66
-- title:
--   Corollary 7.4 — mixed strategies are independent
-- statement:
--   Let $(\Omega,\mathcal B,(\mathcal J_i),(p_i))$ be a randomizing structure for a finite set $N$ of players satisfying Assumption II, with finite pure strategy sets $S_j$. Let $(s_1,\dots,s_n)$ be an $n$-tuple of **mixed** strategies. Then the $s_j$ are independent: for every pure profile $a\in S$, every player $k$, and every choice of $B_j \in \{\{s_j=a_j\},\ \Omega\}$,
--   $$p_k\Big(\bigcap_{j\in N} B_j\Big) = \prod_{j\in N} p_k(B_j).$$
--
--   So strategies pegged on secret events are uncorrelated under everyone's beliefs, as classical mixed strategies are; it is what makes the payoff of an $n$-tuple of objective mixed strategies equal to the classical payoff $F(\sigma)$ of the corresponding distributions.
--
--   **Formalization Note** "The $s_i$ are independent" is read as the paper's notion of *uncorrelated* strategies (p. 75): for every $a\in S$ the $n$ events $\{s_j = a_j\}$ are independent. Because the $S_j$ are finite this is the same as independence of the $s_j$ as random variables under every $p_k$. The corollary is cited on p. 83 under the misprint "Corollary 8.4". Assumption II is the paper's standing assumption and is included, although the proof does not use it.
-- source:
--   R. J. Aumann, Subjectivity and Correlation in Randomized Strategies, J. Math. Econ. 1 (1974) 67–96, https://doi.org/10.1016/0304-4068(74)90037-8, p. 83 (PDF p. 17), Corollary 7.4; "uncorrelated" defined p. 75 (PDF p. 9)

import Mathlib
import Definitions.Def_Aumann1974_TwoPerson_RandomizingStructure

namespace Aumann1974.TwoPerson

open MeasureTheory

/-- **Corollary 7.4** (Aumann 1974, *Subjectivity and Correlation in Randomized Strategies*,
J. Math. Econ. 1, p. 83, PDF p. 17; cited on p. 83 under the misprint "Corollary 8.4"): let
`(s₁, …, sₙ)` be an `n`-tuple of mixed strategies. Then the `sᵢ` are independent.

**Formalization Note.** "The `sᵢ` are independent" is read as the paper's *uncorrelated*
(p. 75, `IsUncorrelated`): for every pure profile `a ∈ S` the `n` events `{sⱼ = aⱼ}` are
independent, i.e. for every player `k` and every choice of `Bⱼ ∈ {{sⱼ = aⱼ}, Ω}`,
`pₖ(⋂ⱼ Bⱼ) = ∏ⱼ pₖ(Bⱼ)`. Because the `Sⱼ` are finite, this coincides with independence of the
`sⱼ` as random variables under every `pₖ`. Mixed strategies are strategies (`IsMixed` implies the
level sets lie in `𝒥ⱼ`). Assumption II, the standing assumption of p. 75, is carried as a
hypothesis although the proof does not use it. -/
theorem mixed_strategies_independent {ι Ω : Type*} [Fintype ι] [DecidableEq ι]
    {mΩ : MeasurableSpace Ω} {S : ι → Type*} [∀ i, Fintype (S i)]
    (R : RandomizingStructure ι Ω mΩ) (hII : AssumptionII R)
    (s : ∀ j, Ω → S j) (hmix : ∀ j, IsMixed R j (s j)) :
    IsUncorrelated R s := by sorry

end Aumann1974.TwoPerson
