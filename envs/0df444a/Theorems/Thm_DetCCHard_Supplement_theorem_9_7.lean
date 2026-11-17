-- Prove2me | Theorems.Thm_DetCCHard_Supplement_theorem_9_7
-- name    : DetCCHard.Supplement.theorem_9_7
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T16:37:45.28462+00:00
-- url     : https://prove2.me/theorems/7901853c-9674-4684-82ae-692f2670f890
-- title:
--   Theorem 9.7 — an additive-$a(T)$ estimator with $2a(S(N, k(N))) < k(N)$ gives a 3-SAT algorithm in time $S(N, k(N))^{O(1)}$
-- statement:
--   There is an absolute integer $A \ge 2$ and, for each fixed clause-density bound $c_s$, an integer $C \ge 1$ with the following property. Suppose a deterministic or bounded-error randomized polynomial-time estimator approximates $D(M)$ with additive error at most a nondecreasing function $a(T)$ on every sufficiently large explicit total Boolean table with $T$ entries; it suffices that it works on square tables whose side length is a power of two. Let the gap $k = k(N) \ge 1$ be an integer function computable in time polynomial in $N + k(N)$. Choose either construction and its size bound:
--   $$
--   S(N, k) = (N + 2)^{C(k+1)} \ \text{(randomized)}, \qquad S(N, k) = (N + 2)^{C A^k} \ \text{(deterministic)}.
--   $$
--   If, for all sufficiently large $N$,
--   $$
--   2a\bigl(S(N, k(N))\bigr) < k(N),
--   $$
--   then 3-SAT on $N$ variables and at most $c_s N$ clauses has an algorithm running in time $S(N, k(N))^{O(1)}$. It is deterministic when both the construction and the estimator are deterministic, and bounded-error randomized otherwise. The exponent may depend on the estimator and the algorithm computing $k$.
--
--   This turns any improvement in approximating communication complexity into a faster 3-SAT algorithm, with an explicit exchange rate between additive error and running time.
--
--   **Formalization Note** The estimator is modelled per Definition 4.1 (polynomial time in $T$ on every tape, outputs comparable in polynomial time with binary rationals of polynomial bit length, guarantee on at least $2/3$ of the tapes). The 3-SAT algorithm reads $N$ in unary and the formula over the variables $0, \dots, N - 1$, plus a random tape; on every tape it halts within $S(N, k(N))^e$ steps and uses at most that many random bits, it answers correctly on at least $2/3$ of the tapes, and it uses no random bits in the deterministic case.
--
--   Differences from the source:
--   - reading: "it suffices for the estimator to work on square tables whose side length is a power of two" → the estimator's running-time bound and accuracy guarantee are assumed only on square power-of-two tables; reason: the stronger of the two readings of "work"
--   - generalization: the estimator's output is comparable in polynomial time with binary rationals (Definition 4.1) → a comparator decides whether the output value is below a given binary rational; reason: deciding "<" is implied by full comparison, so more estimators qualify
--   - generalization: 3-CNF formula (three literals per clause) → every clause has at most three literals; reason: formulas with exactly three literals per clause are a special case
--   - encoding: 3-SAT on N variables and at most c_s N clauses → formulas over the variables 0, …, N − 1 with at most c_s N clauses, input N in unary followed by CookPvsNP.encodeCNF; reason: renaming variables is polynomial-time
--   - encoding: deterministic / bounded-error randomized algorithms and estimators → machines in the published Cook model with a random tape of input-dependent length; deterministic means tape length 0; bounded error means correct on at least 2/3 of the tapes; reason: the conventions of §4.1
--   - encoding: k computable in time polynomial in N + k(N) → a machine reading N in unary and writing k(N) in binary within (N + k(N))^{c_k} + c_k steps; reason: the input N has length N in unary
--   - encoding: running time S(N, k(N))^{O(1)} → an exponent e chosen after the estimator, k and the construction, time and tape length ≤ S(N, k(N))^e for every N; reason: S ≥ 2, so constant overheads (small N) are absorbed
-- source:
--   Gaspers–He–Mackenzie, NP-Hardness and Additive Inapproximability of Deterministic Communication Complexity, arXiv:2508.05597 (held version, sha256 ad552d13…), Theorem 9.7, pp.41–42

import Mathlib
import Definitions.Def_CookPvsNP_defs
import Definitions.Def_DetCCHard_commCost
import Definitions.Def_DetCCHard_CodeSym
import Definitions.Def_DetCCHard_Is3CNF
import Definitions.Def_DetCCHard_Supplement_Estimator

namespace DetCCHard.Supplement

open DetCCHard

/-- **Theorem 9.7 (From approximation algorithms to 3-SAT algorithms)** (Gaspers–He–Mackenzie, arXiv:2508.05597, held version sha256 ad552d13…a4a03, Theorem 9.7,
pp.41–42). There is an effective absolute integer `A ≥ 2` and, for each fixed clause-density bound
`c_s`, an effective integer `C ≥ 1` with the following property. Suppose a deterministic or
bounded-error randomized polynomial-time estimator approximates `D(M)` with additive error at most
a nondecreasing function `a(T)` on every sufficiently large explicit total Boolean table with `T`
entries. Let the gap `k = k(N) ≥ 1` be an integer function computable in time polynomial in
`N + k(N)`. Choose either construction and its size bound: randomized, `S(N, k) = (N + 2)^{C(k+1)}`;
deterministic, `S(N, k) = (N + 2)^{C A^k}`. If, for all sufficiently large `N`,
`2 a(S(N, k(N))) < k(N)`, then 3-SAT on `N` variables and at most `c_s N` clauses has an algorithm
running in time `S(N, k(N))^{O(1)}`. It is deterministic when both the construction and the
estimator are deterministic, and bounded-error randomized otherwise. The exponent may depend on the
estimator and the algorithm computing `k`. It suffices for the estimator to work on square tables
whose side length is a power of two.

**Formalization Note** `det = true` selects the deterministic construction. The estimator is an
`Estimator` with `IsAdditive a` (Definition 4.1: worst-case polynomial time in `T`, outputs
comparable in polynomial time with binary rationals of polynomial bit length, guarantee on at least
`2/3` of the tapes), required only on square power-of-two tables, as the last sentence allows.
`k` is computed by a published one-tape machine from `N` in unary, writing `k(N)` in binary within
`(N + k(N))^{c_k} + c_k` steps. The 3-SAT algorithm is a machine reading `randInput` of
`encodeSparseInstance N Φ` (`N` in unary, then the formula) and a tape whose length `ℓ` depends on
the input only; on every formula with variables among `0, …, N − 1`, at most three literals per
clause and at most `c_s N` clauses, for every `N`, it halts on every tape within `S(N, k(N))^e`
steps, uses at most that many random bits, and accepts exactly when the formula is satisfiable on at
least `2/3` of the tapes; it uses no random bits when the construction and the estimator are
deterministic. `c_s` is real. -/
theorem theorem_9_7 :
    ∃ A : ℕ, 2 ≤ A ∧ ∀ cs : ℝ, ∃ C : ℕ, 1 ≤ C ∧
      ∀ (Est : Estimator) (a : ℕ → ℝ), Monotone a → Est.IsAdditive a →
      ∀ k : ℕ → ℕ, (∀ N, 1 ≤ k N) →
        (∃ (Γk : Type) (_ : Fintype Γk) (ι₁ : Unit ↪ Γk) (ι₂ : CodeSym ↪ Γk)
          (Mk : CookPvsNP.TM Γk) (ck : ℕ), ∀ N : ℕ,
            RunsWithin Mk ι₁ ι₂ (List.replicate N ()) ((N + k N) ^ ck + ck) (natBits (k N))) →
      ∀ det : Bool,
        let S : ℕ → ℕ → ℕ := fun N k' =>
          if det then (N + 2) ^ (C * A ^ k') else (N + 2) ^ (C * (k' + 1))
        (∃ N₀ : ℕ, ∀ N, N₀ ≤ N → 2 * a (S N (k N)) < (k N : ℝ)) →
        ∃ (e : ℕ) (Γ : Type) (_ : Fintype Γ) (ι : Option (CookPvsNP.SatSym ⊕ Bool) ↪ Γ)
          (Alg : CookPvsNP.TM Γ) (ℓ : List CookPvsNP.SatSym → ℕ),
          (det = true → Est.IsDeterministic → ∀ x, ℓ x = 0) ∧
          ∀ (N : ℕ) (Φ : CookPvsNP.CNF), Is3CNF Φ → (∀ Cl ∈ Φ, ∀ lit ∈ Cl, lit.2 < N) →
            (Φ.length : ℝ) ≤ cs * N →
            let x := encodeSparseInstance N Φ
            ℓ x ≤ S N (k N) ^ e ∧
            (∀ tape : Fin (ℓ x) → Bool,
              Alg.HaltsWithin (S N (k N) ^ e) ((randInput x (List.ofFn tape)).map ι)) ∧
            (2 / 3 : ℚ) ≤ tapeFrac (ℓ x) (fun tape =>
              DecidesWithin Alg ι (randInput x (List.ofFn tape)) (S N (k N) ^ e)
                Φ.Satisfiable) := by sorry

end DetCCHard.Supplement
