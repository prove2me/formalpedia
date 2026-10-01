-- Prove2me | Theorems.Thm_Aumann1974_TwoPerson_prob_profile_factor
-- name    : Aumann1974.TwoPerson.prob_profile_factor
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-27T10:45:56.362099+00:00
-- url     : https://prove2.me/theorems/cbc18ddc-0206-480c-b759-d588f5d53a31
-- title:
--   Lemma 7.3 — $p_i\{s=a\}$ factors when every opponent of $i$ plays a mixed strategy
-- statement:
--   Let $(\Omega,\mathcal B,(\mathcal J_i),(p_i))$ be a randomizing structure for a finite set $N$ of players satisfying Assumption II, with finite pure strategy sets $S_j$. Let $(s_1,\dots,s_n)$ be an $n$-tuple of strategies and let $a\in S$ be a pure strategy profile. Suppose that for some $i\in N$ every $s_j$ with $j\ne i$ is mixed ($s_i$ itself need not be). Then
--   $$p_i\{s=a\} = p_i\{s_i=a_i\}\;p_i\{s_j=a_j \text{ for all } j\ne i\} = p_i\{s_1=a_1\}\cdots p_i\{s_n=a_n\}.$$
--
--   The lemma says that under player $i$'s own beliefs, the strategy of $i$ cannot be correlated with the mixed strategies of the others, however $i$ pegs it on his information. It is the step that lets expected payoffs against mixed opponents be computed from the marginal distributions, which is what the proofs of Proposition 4.3 and Proposition 5.1 need.
--
--   **Formalization Note** The paper prints "$j \ne 1$" in the middle term; the proof ("W.l.o.g. let $i=1$") shows that $j\ne i$ is meant, and that is what is stated; likewise the printed first factor "$p_i\{s=s_1\}$" of the last term is $p_i\{s_1=a_1\}$. Both equalities are part of the conclusion. Assumption II is the paper's standing assumption and is included, although the proof does not use it.
-- source:
--   R. J. Aumann, Subjectivity and Correlation in Randomized Strategies, J. Math. Econ. 1 (1974) 67–96, https://doi.org/10.1016/0304-4068(74)90037-8, p. 82 (PDF p. 16), Lemma 7.3 (misprint "j ≠ 1" for "j ≠ i"); proof p. 83 (PDF p. 17)

import Mathlib
import Definitions.Def_Aumann1974_TwoPerson_RandomizingStructure

namespace Aumann1974.TwoPerson

open MeasureTheory

/-- **Lemma 7.3** (Aumann 1974, *Subjectivity and Correlation in Randomized Strategies*,
J. Math. Econ. 1, p. 82, PDF p. 16): let `(s₁, …, sₙ)` be an `n`-tuple of strategies, and let
`a ∈ S`. For some `i ∈ N`, suppose that all the `sⱼ` except possibly `sᵢ` are mixed. Then
`pᵢ{s = a} = pᵢ{sᵢ = aᵢ} pᵢ{sⱼ = aⱼ for all j ≠ i} = pᵢ{s₁ = a₁} ⋯ pᵢ{sₙ = aₙ}`.

**Formalization Note.** The paper prints "`j ≠ 1`" in the middle term; the proof ("W.l.o.g. let
`i = 1`") shows `j ≠ i` is meant, and that is what is stated. The first factor of the last term
is printed "`pᵢ{s = s₁}`"; it is `pᵢ{s₁ = a₁}`. Both equalities are part of the
conclusion. The pure profile is `a` (the paper reuses the letter `s`). Every `sⱼ` is a strategy of
`j` (level sets in `𝒥ⱼ`); `sⱼ` for `j ≠ i` is mixed. Assumption II, the standing assumption of
p. 75, is carried as a hypothesis although the proof does not use it. -/
theorem prob_profile_factor {ι Ω : Type*} [Fintype ι] [DecidableEq ι]
    {mΩ : MeasurableSpace Ω} {S : ι → Type*} [∀ i, Fintype (S i)]
    (R : RandomizingStructure ι Ω mΩ) (hII : AssumptionII R)
    (s : ∀ j, Ω → S j) (hs : ∀ j, IsStrategy R j (s j)) (a : ∀ j, S j) (i : ι)
    (hmix : ∀ j, j ≠ i → IsMixed R j (s j)) :
    R.p i {ω | ∀ j, s j ω = a j} =
        R.p i {ω | s i ω = a i} * R.p i {ω | ∀ j, j ≠ i → s j ω = a j} ∧
      R.p i {ω | s i ω = a i} * R.p i {ω | ∀ j, j ≠ i → s j ω = a j} =
        ∏ j, R.p i {ω | s j ω = a j} := by sorry

end Aumann1974.TwoPerson
