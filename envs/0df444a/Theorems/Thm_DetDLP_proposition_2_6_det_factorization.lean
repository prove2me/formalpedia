-- Prove2me | Theorems.Thm_DetDLP_proposition_2_6_det_factorization
-- name    : DetDLP.proposition_2_6_det_factorization
-- status  : Open
-- author  : @Bingsheng
-- created : 2026-11-23T09:19:36.121355+00:00
-- url     : https://prove2.me/theorems/1a4d8ed3-c982-4607-bffa-778ca37364a9
-- title:
--   Proposition 2.6: Deterministic $2^{O(n/\sqrt{\log n})}$ Integer Factorization
-- statement:
--   There exist a deterministic multitape Turing machine $M$ and a constant $K \in \mathbb{N}$ such that for every integer $N \ge 2$, setting $n = \lceil \log_2(N + 1) \rceil$, machine $M$ on the canonical binary encoding of $N$ outputs the sorted list of prime factors of $N$ with multiplicity within worst-case time and space
--
--   $$\text{time} \le 2^{K n / \sqrt{\log_{\mathrm{safe}} n}}, \qquad \text{space} \le K(n + 1)^K.$$
--
--   In the prime-field DLP algorithm, deterministic factorization of $p - 1$ is used to construct a primitive root modulo $p$ without number-theoretic conjectures.
--
--   **Formalization Note** The output list is Mathlib's `Nat.primeFactorsList N` encoded via `encodeNatListBin`.
-- source:
--   S. Liu, B. Zhang, and K. Ren, "A Deterministic Subexponential-time Algorithm for the Discrete Logarithm Problem", Zhejiang University Preprint, 23 November 2026, Section 2.3, Proposition 2.6 (pp. 10–11)

import Mathlib
import Definitions.Def_DetDLP_Machine

set_option autoImplicit false

namespace DetDLP

open OAI.Algorithms.SubexponentialSAT
open OAI.Algorithms.SubexponentialSAT.Computation
open OAI.Algorithms.SubexponentialSAT.SqrtLogSpace

theorem proposition_2_6_det_factorization :
    ∃ (M : PrimitiveMachine) (out : Fin M.tapeCount) (K : ℕ),
      ∀ N : ℕ, 2 ≤ N →
        let n := bitLen (N + 1)
        RunsWithin M out (countWord N) (encodeNatListBin N.primeFactorsList)
          ((2 : ℝ) ^ ((K : ℝ) * (n : ℝ) / Real.sqrt (logSafe (n : ℝ))))
          (polyBound K n) := by sorry

end DetDLP
