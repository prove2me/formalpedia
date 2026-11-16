-- Prove2me | Theorems.Thm_CNFLearning873_Valiant_Supplement_theorem_6_2
-- name    : CNFLearning873.Valiant.Supplement.theorem_6_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T21:40:59.399721+00:00
-- url     : https://prove2.me/theorems/aed9cdd8-c56b-4fb5-89ab-398f99a7c43b
-- title:
--   Theorem 6.2 (companion theorem; not used in the proof of the goal) — minimax sample lower bound
-- statement:
--   For each integer $k\ge3$, there is a coefficient $c_k>0$, uniform over every $0<\varepsilon_0<1/4$, such that for all sufficiently large $n\ge n_0(k,\varepsilon_0)$ there is a nonempty family of satisfiable $n$-variable $(k,k)$-CNFs with the following property. For every sample count satisfying
--
--   $$T<c_k\frac n{\varepsilon_0\log_2n}$$
--
--   and every sample-only randomized learner, some target in that family has probability strictly less than $1/3$ of a satisfiable output within TV distance $\varepsilon_0$. Both learning-sample randomness and arbitrary internal randomization are included. The family precedes the learner, which may know the family but cannot inspect the unknown target. There is no computational or output-width restriction. This is the paper's minimax companion lower bound.
--
--   Differences from the source:
--   - encoding: Boolean assignments on a named n-variable set → assignments on Fin n, using the published CNF and nonempty uniform-solution laws; reason: variable relabeling changes no instance; output satisfiability prevents an undefined uniform law
--   - encoding: Omega_k necessary samples with target chosen after the learner → a positive k-only coefficient with strict T threshold and failure of confidence one third; reason: Appendix B has strict failure greater than two thirds; positive coefficient rescaling and log-base conversion preserve all regimes
--   - encoding: all sufficiently large n → an existential n0 at least 2 before n; reason: keeps the logarithm positive without excluding any asymptotic instance
-- source:
--   Weiming Feng, Yixiao Yu, Yiyao Zhang, STOC 2027 submission #873 (October 2026), Theorem 6.2, printed p.27 = 1-based PDF p.27; https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/873.pdf

import Definitions.Def_CNFLearning873_Valiant_Supplement_LearningModel

namespace CNFLearning873.Valiant.Supplement

/-- Theorem 6.2, p.27 = PDF p.27, with the full minimax quantifier order. -/
theorem theorem_6_2 (k : ℕ) (hk : 3 ≤ k) :
    ∃ c : ℝ, 0 < c ∧ ∀ ε : ℝ, 0 < ε → ε < 1 / 4 →
    ∃ n₀ : ℕ, 2 ≤ n₀ ∧ ∀ n : ℕ, n₀ ≤ n →
    ∃ family : Finset (CNF n), family.Nonempty ∧
      (∀ F ∈ family, KD F k k ∧ (solutions F).Nonempty) ∧
      ∀ T : ℕ, (T : ℝ) < c * ((n : ℝ) / log₂ n) / ε →
      ∀ A : Learner n T, ∃ F ∈ family, ∃ h : (solutions F).Nonempty,
        learnerSuccess F h ε A < 1 / 3 := by sorry

end CNFLearning873.Valiant.Supplement
