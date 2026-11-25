-- Prove2me | Theorems.Thm_DetDLP_proposition_2_6_from_appendix_d
-- name    : DetDLP.proposition_2_6_from_appendix_d
-- status  : Proved
-- author  : @Bingsheng
-- created : 2026-11-24T07:21:56.579811+00:00
-- url     : https://prove2.me/theorems/889d5050-e28b-4ef0-82cf-95676174eb66
-- title:
--   Proposition 2.6: Deterministic $2^{O(n/\sqrt{\log n})}$ Integer Factorization (under Appendix D.4)
-- statement:
--   Assume the two contraction interfaces of OpenAI Appendix D.4 (`OpenAIAppendixDPremise`). Then there exist a deterministic multitape Turing machine $M$ and a constant $K \in \mathbb{N}$ such that for every integer $N \ge 2$, setting $n = \lceil \log_2(N + 1) \rceil$, machine $M$ on the canonical binary encoding of $N$ outputs the sorted list of prime factors of $N$ with multiplicity (`Nat.primeFactorsList N` encoded via `encodeNatListBin`) within worst-case time and space
--
--   $$\text{time} \le 2^{K n / \sqrt{\log_{\mathrm{safe}} n}}, \qquad \text{space} \le K(n + 1)^K.$$
-- source:
--   S. Liu, B. Zhang, and K. Ren, "A Deterministic Subexponential-time Algorithm for the Discrete Logarithm Problem", Section 2.3, Proposition 2.6 (pp. 10–11); conditional on OpenAI (Oct 25, 2026), Appendix D, Section D.4.

import Definitions.Def_DetDLP_OpenAIAppendixD
import Definitions.Def_DetDLP_Machine

set_option autoImplicit false

namespace DetDLP

open OAI.Algorithms.SubexponentialSAT
open OAI.Algorithms.SubexponentialSAT.Computation
open OAI.Algorithms.SubexponentialSAT.SqrtLogSpace

theorem proposition_2_6_from_appendix_d (hOAI : OpenAIAppendixDPremise) :
    ∃ (M : PrimitiveMachine) (out : Fin M.tapeCount) (K : ℕ),
      ∀ N : ℕ, 2 ≤ N →
        let n := bitLen (N + 1)
        RunsWithin M out (countWord N) (encodeNatListBin N.primeFactorsList)
          ((2 : ℝ) ^ ((K : ℝ) * (n : ℝ) / Real.sqrt (logSafe (n : ℝ))))
          (polyBound K n) := by sorry

end DetDLP
