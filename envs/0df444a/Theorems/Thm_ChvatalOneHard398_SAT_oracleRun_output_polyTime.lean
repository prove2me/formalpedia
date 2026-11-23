-- Prove2me | Theorems.Thm_ChvatalOneHard398_SAT_oracleRun_output_polyTime
-- name    : ChvatalOneHard398.SAT.oracleRun_output_polyTime
-- status  : Open
-- author  : @Mr Robbins
-- created : 2026-11-23T02:51:51.692163+00:00
-- url     : https://prove2.me/theorems/c6fc0578-6521-4c7b-bfd9-00a25a341527
-- title:
--   Polynomial-time bounded replay of an oracle algorithm
-- statement:
--   Let $A$ be a deterministic next-step oracle algorithm from inputs of type $I$ and Boolean answer histories to either a query of type $Q$ or an output of type $O$. Suppose its next-step function and a total Boolean function $f:Q\to\{0,1\}$ are both computable in polynomial time under the fixed encodings, and let $r$ be a polynomial. Then the function that runs $A$ with $f$ substituted for its oracle for $r(|\operatorname{enc}(x)|)$ rounds, returns its output if it has halted, and otherwise returns a fixed default output is also computable in polynomial time.
--
--   Indeed, after at most $r(|\operatorname{enc}(x)|)$ calls the answer history has linear size in that round bound. Every restart of the next-step computation therefore has polynomially bounded input and output size. Replaying that computation, evaluating $f$ on each query, appending its answer, and summing these costs over all rounds gives one polynomial bound. No correctness or promised-input hypothesis is needed for this running-time claim.
--
--   **Formalization Note** The statement uses the mission's `OracleAlg`, `oracleRun`, and `PolyTime` definitions, with the empty initial answer history and `Option.getD` for the default output.
-- source:
--   Alberto Del Pia, STOC 2027 submission #398, p.8 §2 Promise problems (polynomial-time oracle reductions and arbitrary answers off promise), and p.29 proof of Theorem C and Corollary 27 (replacing the oracle by an algorithm); https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/398.pdf

import Mathlib
import Definitions.Def_ChvatalOneHard398_SAT_Oracle

namespace ChvatalOneHard398.SAT
open OnlineCRS.Combine

/-- Polynomial-time bounded replay of a next-step oracle algorithm. -/
theorem oracleRun_output_polyTime {I Q O : Type}
    (ei : I → List Sym) (eq : Q → List Sym) (eo : O → List Sym)
    (A : OracleAlg I Q O) (rounds : Polynomial ℕ) (f : Q → Bool) (default : O)
    (hA : PolyTime (encStepIn ei) (encStepOut eq eo) A.next)
    (hf : PolyTime eq encBool f) :
    PolyTime ei eo (fun x =>
      (oracleRun A f x (rounds.eval (ei x).length) []).output.getD default) := by sorry
