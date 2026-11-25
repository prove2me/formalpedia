-- Prove2me | Theorems.Thm_DetDLP_ec_moment_uniform_query_program
-- name    : DetDLP.ec_moment_uniform_query_program
-- status  : Open
-- author  : @Bingsheng
-- created : 2026-11-25T13:57:29.411166+00:00
-- url     : https://prove2.me/theorems/a88ebafc-72b9-5706-a5b7-31ba46456830
-- title:
--   Uniform polynomial-time programs for elliptic-curve moment queries
-- statement:
--   There is one positive bound and a pair of polynomial-time programs encoding the graph and its port queries, uniformly for all four elliptic-curve moment queries. The exact number of satisfying assignments equals the corresponding moment value.
-- source:
--   S. Liu, B. Zhang, and K. Ren, "A Deterministic Subexponential-time Algorithm for the Discrete Logarithm Problem", Zhejiang University Preprint, 23 November 2026, Section 2.4, Section 3 & Section 4, Lemma 2.4, Theorem 3.1 & Theorem 1.1 (pp. 9–19)

import Definitions.Def_DetDLP_S8I_ECMomentGraph

set_option autoImplicit false
open DetDLP
open OAI.Algorithms.SubexponentialSAT OAI.Algorithms.SubexponentialSAT.Computation
open OAI.Algorithms.SubexponentialSAT.SqrtLogSpace

theorem DetDLP.ec_moment_uniform_query_program :
    ∃ (make port : List Bool → List Bool) (L : ℕ), 0 < L ∧
      Groundwork.PolyT make ∧ Groundwork.PolyT port ∧
      ∀ (p : ℕ) [Fact p.Prime], 3 < p → ∀ (E : WeierstrassCurve (ZMod p)) [E.IsElliptic]
        (j : Fin 4) (T : ℕ) (η : List Bool), T ≤ p →
        η.length ≤ blockCount (bitLen p)*4*bitLen p →
        S8C.Realizes make port L (S8I.ECMoment.word E j T η) (bitLen p)
          (S8I.ECQueryCount.value p (blockCount (bitLen p)) E T η j) := by sorry
