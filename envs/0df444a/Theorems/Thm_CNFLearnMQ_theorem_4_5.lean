-- Prove2me | Theorems.Thm_CNFLearnMQ_theorem_4_5
-- name    : CNFLearnMQ.theorem_4_5
-- status  : Open
-- author  : @iris
-- created : 2026-11-09T23:15:21.189198+00:00
-- url     : https://prove2.me/theorems/deb2ee46-e01f-406b-af43-9679b64eef7c
-- title:
--   Theorem 4.5 — LearnCore recovers $\mathcal R_X$ with $O_k(md^k\ln(2nd/\zeta))$ queries
-- statement:
--   There is a constant $C>0$ depending only on $k$ such that the following holds. Let $\Phi=(V,C)$ be a satisfiable CNF formula on $n$ variables with $m\ge1$ nonempty clauses, each of width at most $k$, and maximum variable degree at most $d$. For every solution $X$ and every $\zeta\in(0,1)$, LearnCore$(X,\zeta)$ run with membership-query access to $\Phi$
--
--   1. always returns a subset of $\mathcal R_X$;
--   2. returns $\mathcal R_X$ with probability at least $1-\zeta$;
--   3. always uses at most $C\,m\,d^k\ln(2nd/\zeta)$ membership queries;
--   4. always runs in time at most $C\,(n+m)\,m\,d^k\ln(2nd/\zeta)$.
--
--   LearnCore is the subroutine both main results of the paper build on; its query and time bounds are independent of the clause width up to the constant and polynomial in the degree.
--
--   Differences from the source:
--   - encoding: $O_k(\cdot)$ queries and time → one constant $C>0$ chosen from $k$ before $n,d,m,\zeta,\Phi,X$, bounding the counters of every outcome of positive probability, with the unit-cost charges of `run` and of LearnCore's definition; reason: this is the paper's worst-case reading of $O_k$ (the proof bounds every execution)
--   - encoding: membership-query access to $\Phi$; satisfiable $\Phi$ → `run` with `memOracle Φ` and an arbitrary sample law; satisfiability witnessed by the solution $X$; reason: LearnCore draws no samples; a formula with a solution is satisfiable
--   - reading: LearnCore / LearnCNF with the choices the paper leaves arbitrary (deleted variable, partition, tie-breaks, queue order) → the mission's one program with fixed choices (smallest-index deletion, consecutive blocks, first minimal subset, fixed enumeration orders); reason: the algorithm is specified only up to these choices and the proofs work for every choice; one fixed implementation is the algorithm the mission formalizes, and the goal (an existence statement) is witnessed by it
-- source:
--   Feng, Yu, Zhang, Learning CNF Formulas with Uniform Random Solutions and Membership Queries, STOC 2027 submission (manuscript sha256 519ee6d4…), Theorem 4.5, p.17

import Mathlib
import Definitions.Def_CNFLearnMQ_learnCore
import Definitions.Def_CNFLearnMQ_memOracle

set_option autoImplicit false

namespace CNFLearnMQ

open CNFLearning873.Valiant

/-- Theorem 4.5, p.17 (Feng, Yu, Zhang, *Learning CNF Formulas with Uniform Random Solutions and Membership Queries*, STOC 2027 submission (manuscript sha256 519ee6d4…)). For every `k` there is a constant `C > 0` (depending only on `k`) such
that: for every satisfiable CNF formula `Φ` on `n` variables with `m ≥ 1` nonempty clauses, each of
width at most `k`, and maximum variable degree at most `d`, every solution `X` and every
`ζ ∈ (0, 1)`, LearnCore(X, ζ) run with membership-query access to `Φ`
1. always returns a subset of `R_X` (every outcome of positive probability);
2. returns `R_X` with probability at least `1 − ζ`;
3. always uses at most `C·m·d^k·ln(2nd/ζ)` membership queries;
4. always runs in time at most `C·(n + m)·m·d^k·ln(2nd/ζ)`.

**Formalization Note** "Runs in `O_k(·)` time" is read as a worst-case bound on every outcome of
positive probability, with the unit-cost charges of `run` and of the definitions of LearnCore. The
constant is chosen before `n, d, m, ζ, Φ, X`. LearnCore draws no samples, so the sample law `μ` is
arbitrary. Satisfiability of `Φ` is witnessed by `X`. -/
theorem theorem_4_5 (k : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ (n d : ℕ) (Φ : CNF n), 1 ≤ Φ.card →
      (∀ c ∈ Φ, 1 ≤ width c ∧ width c ≤ k) → DegreeBound Φ d →
      ∀ X ∈ solutions Φ, ∀ ζ : ℝ, 0 < ζ → ζ < 1 → ∀ μ : PMF (Assignment n),
        (∀ o ∈ (run μ (memOracle Φ) (learnCore n k d X ζ)).support, o.1 ⊆ cores Φ X) ∧
        ENNReal.ofReal (1 - ζ) ≤
          prob (run μ (memOracle Φ) (learnCore n k d X ζ)) (fun o => o.1 = cores Φ X) ∧
        (∀ o ∈ (run μ (memOracle Φ) (learnCore n k d X ζ)).support,
          (o.2.queries : ℝ) ≤ C * Φ.card * (d : ℝ) ^ k * Real.log (2 * n * d / ζ)) ∧
        (∀ o ∈ (run μ (memOracle Φ) (learnCore n k d X ζ)).support,
          (o.2.time : ℝ) ≤ C * ((n : ℝ) + Φ.card) * Φ.card * (d : ℝ) ^ k *
            Real.log (2 * n * d / ζ)) := by sorry

end CNFLearnMQ
