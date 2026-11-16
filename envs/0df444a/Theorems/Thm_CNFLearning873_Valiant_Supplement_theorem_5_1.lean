-- Prove2me | Theorems.Thm_CNFLearning873_Valiant_Supplement_theorem_5_1
-- name    : CNFLearning873.Valiant.Supplement.theorem_5_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T21:39:45.537825+00:00
-- url     : https://prove2.me/theorems/c709e385-3d4a-4003-881a-2badc53a62ad
-- title:
--   Theorem 5.1 (companion theorem; not used in the proof of the goal) — Valiant sample lower bound
-- statement:
--   Fix any real $t>1$. For every sufficiently large integer $k$, there are an integer $d\ge1$ satisfying the exact local lemma inequality
--
--   $$k\ge(1+1/t)\log_2d+2\log_2k+t-3\log_2t+5$$
--
--   and a constant $c_{k,t}>0$, chosen before $\varepsilon_0$, such that for every $0<\varepsilon_0<1/4$ and all sufficiently large $n$ there is a satisfiable $(k,d)$-CNF $F$ for which Valiant's success probability is strictly less than $1/3$ whenever
--
--   $$T<c_{k,t}\frac{(n/\log_2 n)^{\lceil t\rceil}}{\varepsilon_0}.$$
--
--   The size threshold may depend on $k,d,\varepsilon_0$, but the coefficient does not depend on $n$ or $\varepsilon_0$. The same hard formula works for every smaller sample count. This is the companion lower bound for Valiant's algorithm.
--
--   Differences from the source:
--   - encoding: Boolean assignments on a named n-variable set → assignments on Fin n, using the published CNF and nonempty uniform-solution laws; reason: variable relabeling changes no instance; output satisfiability prevents an undefined uniform law
--   - encoding: an asymptotic necessary sample count at confidence at least one third → a positive coefficient and strict T below its threshold imply success strictly below one third; reason: taking a smaller positive coefficient in the source bound of p.26 avoids equality at the confidence boundary and preserves the full Omega claim
--   - encoding: all sufficiently large n → an existential threshold n0 at least 2 before n; reason: only fixes the logarithm domain; every sufficiently large size is retained
-- source:
--   Weiming Feng, Yixiao Yu, Yiyao Zhang, STOC 2027 submission #873 (October 2026), Theorem 5.1, printed p.21 = 1-based PDF p.21; https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/873.pdf

import Definitions.Def_CNFLearning873_Valiant_Supplement_LearningModel

namespace CNFLearning873.Valiant.Supplement

/-- Theorem 5.1, p.21 = PDF p.21. The coefficient is uniform in ε, n and sample count.
Strictly fewer samples than the lower-bound threshold cannot attain confidence 1/3. -/
theorem theorem_5_1 :
    ∀ t : ℝ, 1 < t → ∃ k₀ : ℕ, ∀ k : ℕ, k₀ ≤ k →
    ∃ d : ℕ, 1 ≤ d ∧ LLLCondition k d t ∧
    ∃ c : ℝ, 0 < c ∧ ∀ ε : ℝ, 0 < ε → ε < 1 / 4 →
    ∃ n₀ : ℕ, 2 ≤ n₀ ∧ ∀ n : ℕ, n₀ ≤ n →
    ∃ F : CNF n, ∃ h : (solutions F).Nonempty, KD F k d ∧
    ∀ T : ℕ, (T : ℝ) < c * ((n : ℝ) / log₂ n) ^ Nat.ceil t / ε →
      eventProb (sampleLaw F h T) (Success F h k ε) < 1 / 3 := by sorry

end CNFLearning873.Valiant.Supplement
