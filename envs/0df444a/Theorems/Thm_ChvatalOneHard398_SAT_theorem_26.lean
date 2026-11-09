-- Prove2me | Theorems.Thm_ChvatalOneHard398_SAT_theorem_26
-- name    : ChvatalOneHard398.SAT.theorem_26
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T10:47:13.484065+00:00
-- url     : https://prove2.me/theorems/e93cfc5d-27d8-41d2-8a92-4fe3989c99bf
-- title:
--   Theorem 26 — decoding with thin-formula queries
-- statement:
--   There is one deterministic polynomial-time oracle algorithm, uniform over all positive-dimensional rational BDD instances, solving bounded distance decoding with factor $1/(4n^{5/2})$ when its satisfiability oracle is required to be correct only on thin constructed formulas:
--
--   $$\operatorname{BDD}_{1/(4n^{5/2})}\le_T^{\mathrm{poly}}\operatorname{SAT}\bigm|_{\mathrm{ThinQuery}}.$$
--
--   Every actual query, on every raw input and for every oracle, equals $F(p,h,H,D,t)$ for valid parameters of Proposition 16. Thinness is not asserted for every query. The computation terminates within a fixed polynomial bound on all raw inputs, whatever the oracle answers outside its promise. This retains both sentences of the theorem.
--
--   Differences from the source:
--   - encoding: a deterministic polynomial-time oracle reduction with unit-cost calls → a polynomial-time next-step map with a fixed polynomial round bound on every input and every oracle; reason: answer-history replay and summing its step costs are polynomially equivalent to the source oracle machine; correctness is separate
--   - encoding: deterministic polynomial time in structured bit size → TM2 polynomial time with fixed, dimension-prefixed, length-framed binary encodings; reason: these encodings are injective and have length linear in the corresponding bit size
--   - encoding: BDD in positive dimension with α∈(0,1), Section 2 → n>0 in the promise while raw dimension-zero and singular inputs still have a uniform polynomial termination bound; reason: the shortest-nonzero-vector decoding regime excludes dimension zero; out-of-promise outputs are arbitrary
--   - encoding: every query is a formula of Proposition 16 → every member of the run trace satisfies ConstructedQuery; reason: the trace contains exactly the queries actually made, including queries from non-promise runs
-- source:
--   Alberto Del Pia, 0/1 integer programming over polytopes of Chvátal rank one is as hard as lattice problems, STOC 2027 submission #398 (October 2026), p.27, Theorem 26; https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/398.pdf

import Mathlib
import Definitions.Def_ChvatalOneHard398_SAT_Oracle

namespace ChvatalOneHard398.SAT

theorem theorem_26 :
    ∃ (A : OracleAlg BDDInput Formula (List ℚ)) (rounds : Polynomial ℕ),
      IsPolyOracle encBDD encFormula encOutput A rounds ∧ SolvesBDDWith A rounds ThinQuery ∧
      ∀ orc x, ∀ F ∈ (oracleRun A orc x (rounds.eval (encBDD x).length) []).queries,
        ConstructedQuery F := by sorry

end ChvatalOneHard398.SAT
