-- Prove2me | Theorems.Thm_ExactLearningSeparation678_Randomized_Supplement_theorem_4_1
-- name    : ExactLearningSeparation678.Randomized.Supplement.theorem_4_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T20:32:51.241041+00:00
-- url     : https://prove2.me/theorems/7cb34450-035c-485a-baa7-a986f9e57651
-- title:
--   Theorem 4.1 (companion theorem) — quantum Booleanization $Q(C)=\Theta(Q_{\mathrm{bool}}(C))$
-- statement:
--   There are absolute constants $a,b>0$ such that for every concept class $C\subseteq\{0,1\}^N$,
--   $$a\,Q_{\mathrm{bool}}(C)\le Q(C)\le b\,Q_{\mathrm{bool}}(C),$$
--   where $Q(C)$ is the bounded-error quantum query complexity of exactly learning $C$ and $Q_{\mathrm{bool}}(C)=\max_{P\subseteq C}Q(b_P)$ is the largest bounded-error quantum query complexity of deciding membership $b_P(c)=1[c\in P]$ of the unknown concept in a subset $P$.
--
--   Quantumly, identifying a concept is therefore no harder, up to a constant factor, than the hardest single yes/no question about it.
--
--   **Formalization Note** The constants precede the coordinate set and the class. $Q(b_P)$ uses the same quantum query model as $Q(C)$, with a Boolean output and success probability at least $2/3$ for every $c\in C$.
--
--   Differences from the source:
--   - encoding: coordinates [N] of C ⊆ {0,1}^N → an arbitrary finite type ι : Type with decidable equality, concepts ι → Bool; reason: a relabeling of [N]; every N, including N = 0, is an instance
--   - encoding: bounded-error quantum and randomized query complexities Q(C), R(C) → the published quantumExactComplexity (QueryAlg, XOR oracle, any finite workspace) and classicalExactComplexity (randomized decision trees, worst-case query bound), success ≥ 2/3 on every target; reason: the mission’s published models of the source’s Q and R
--   - encoding: Q(C) = Θ(Q_bool(C)) for every C → a, b > 0 quantified before ι and C with a·Q_bool ≤ Q ≤ b·Q_bool; reason: the source’s Θ is uniform over all classes
-- source:
--   Srinivasan Arunachalam, Amin Shiraz Gilani, Nikhil S. Mande, STOC 2027 submission #678 (October 2026), Theorem 4.1, p.29; Booleanization, p.28; https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/678.pdf

import Definitions.Def_ExactLearningSeparation678_Randomized_Supplement_Models

open Classical
set_option autoImplicit false

namespace ExactLearningSeparation678.Randomized.Supplement

open QAlgorithms.Learning

/-- Theorem 4.1 (Quantum Booleanization), p.29: `Q(C) = Θ(Q_bool(C))` uniformly: absolute
`a, b > 0`, fixed before `N` and `C`, with `a · Q_bool(C) ≤ Q(C) ≤ b · Q_bool(C)`. -/
theorem theorem_4_1 : ∃ a b : ℝ, 0 < a ∧ 0 < b ∧
    ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (C : Finset (ι → Bool)),
      a * (Qbool C : ℝ) ≤ (quantumExactComplexity C : ℝ) ∧
      (quantumExactComplexity C : ℝ) ≤ b * (Qbool C : ℝ) := by sorry

end ExactLearningSeparation678.Randomized.Supplement
