-- Prove2me | Theorems.Thm_CNFLearning873_Valiant_Supplement_theorem_6_5
-- name    : CNFLearning873.Valiant.Supplement.theorem_6_5
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T21:44:32.505972+00:00
-- url     : https://prove2.me/theorems/5babb4fb-e9f2-4d20-8233-6cbc27dbc666
-- title:
--   Theorem 6.5 (companion theorem; not used in the proof of the goal) — oracle learner sample, query and time bounds
-- statement:
--   For integers $k,d\ge3$, every $0<\varepsilon,\delta<1$, and every $n\ge n_0(k)$, the specified randomized oracle learner learns every satisfiable $n$-variable $(k,d)$-CNF with TV error at most $\varepsilon$ and probability at least $1-\delta$. There is no local lemma assumption. Its resources are
--
--   $$T=O_{k,d}\!\left(\frac n\varepsilon\log_2^4\frac n{\varepsilon\delta}\right),\qquad
--   \#\mathrm{Count}\le\mathrm{poly}_{k,d}(n,1/\varepsilon,\log_2(1/\delta))\exp\!\left(O_k\!\left(\frac n{\log_2n}\right)\right).$$
--
--   Every query has the original $n$ variables, width at most $k$, and at most $O_{k,d}(n^k+n\log_2(n/(\varepsilon\delta)))$ clauses. The output may have larger width. Conditional on the whole deterministic counting bound recalled as Theorem 6.4, the same learner has worst-case time
--
--   $$\mathrm{poly}_{k,d}(n,1/\varepsilon,\log_2(1/\delta))\exp\!\left(O_k\!\left(\frac{n\log_2\log_2 n}{\sqrt{\log_2n}}\right)\right).$$
--
--   The formal statement replaces each asymptotic notation by explicit positive coefficients, a natural polynomial degree and a sufficiently large threshold, before the varying inputs. Exponential rates and the initial size threshold are chosen before $d$; polynomial coefficients and degrees may depend on $k,d$. The conditional implementation rate and threshold may additionally depend on the supplied counting implementation, whose correctness is the exact oracle semantics and whose time is charged for each actual query. The sampler truncates after the stated rejection limit and returns True on abort; success includes both product-sample randomness and internal randomness. The external counting theorem is a premise of the time implication, not a newly asserted milestone.
--
--   Differences from the source:
--   - encoding: Boolean assignments on a named n-variable set → assignments on Fin n, using the published CNF and nonempty uniform-solution laws; reason: variable relabeling changes no instance; output satisfiability prevents an undefined uniform law
--   - encoding: O, poly and sufficiently large n bounds with the specified dependencies → positive real coefficients, natural polynomial degrees and explicit thresholds preceding varying inputs; reason: the polynomial envelope is equivalent on the positive source domain; exponential coefficients and thresholds are uniform in d as required
--   - encoding: bounded-rejection implementation and its worst-case running time → finite random/count programs with accumulated query reports and conservative ordinary-operation charges; conditional time substitutes the counting cost for every query; reason: charges subset enumeration, conditional counts, repeated draws, greedy scans and output construction, without assuming a resource guarantee in a learner structure; the external counting implication remains conditional
-- source:
--   Weiming Feng, Yixiao Yu, Yiyao Zhang, STOC 2027 submission #873 (October 2026), Theorem 6.5, printed p.27 = 1-based PDF p.27; https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/873.pdf

import Definitions.Def_CNFLearning873_Valiant_Supplement_OracleLearner

namespace CNFLearning873.Valiant.Supplement

/-- Theorem 6.5, pp.27-30 = PDF pp.27-30. The fixed program is sample-only, returns True
on rejection abort, and is interpreted with exact width-at-most-k counting queries. Constants
in the exponential rates and the initial threshold precede d. No LLL assumption is imposed.
The second conjunct is conditional on the externally recalled deterministic counting bound. -/
theorem theorem_6_5 (k : ℕ) (hk : 3 ≤ k) :
    ∃ A : ℝ, 0 < A ∧ ∃ n₀ : ℕ, 3 ≤ n₀ ∧
    (∀ d : ℕ, 3 ≤ d → ∃ C : ℝ, 0 < C ∧ ∃ p : ℕ,
      ∀ n : ℕ, n₀ ≤ n → ∀ ε δ : ℝ, 0 < ε → ε < 1 → 0 < δ → δ < 1 →
        (learningSamples n k d ε δ : ℝ) ≤ C * sampleScale65 n ε δ ∧
        (∀ xs : Fin (learningSamples n k d ε δ) → Assignment n,
          ∀ z : Report n (CNF n),
          implemented (rejectionLimit n (rounds n k d ε δ) δ) (oracleLearner k d ε δ xs) z ≠ 0 →
            (z.queries.length : ℝ) ≤ C * polynomialScale n ε δ p *
              Real.exp (A * oracleExponent n) ∧
            ∀ Q ∈ z.queries, (∀ c ∈ Q, width c ≤ k) ∧
              (Q.card : ℝ) ≤ C * queryScale n k ε δ) ∧
        (∀ F : CNF n, KD F k d → ∀ h : (solutions F).Nonempty,
          1 - δ ≤ oracleSuccess F h k d ε δ)) ∧
    (∀ cost : (n : ℕ) → CNF n → ℕ,
      (∃ B : ℝ, 0 < B ∧ ∃ q nCount : ℕ, ∀ n : ℕ, nCount ≤ n →
        ∀ Q : CNF n, (∀ c ∈ Q, width c ≤ k) →
          (cost n Q : ℝ) ≤ B * ((n + Q.card + 1 : ℕ) : ℝ) ^ q *
            Real.exp (B * timeExponent n)) →
      ∃ Btime : ℝ, 0 < Btime ∧ ∃ nTime : ℕ, n₀ ≤ nTime ∧
      ∀ d : ℕ, 3 ≤ d → ∃ D : ℝ, 0 < D ∧ ∃ p : ℕ,
        ∀ n : ℕ, nTime ≤ n → ∀ ε δ : ℝ,
        0 < ε → ε < 1 → 0 < δ → δ < 1 →
        ∀ xs : Fin (learningSamples n k d ε δ) → Assignment n,
        ∀ z : Report n (CNF n),
          implemented (rejectionLimit n (rounds n k d ε δ) δ) (oracleLearner k d ε δ xs) z ≠ 0 →
          (reportTime (cost n) z : ℝ) ≤ D * polynomialScale n ε δ p *
            Real.exp (Btime * timeExponent n)) := by sorry

end CNFLearning873.Valiant.Supplement
