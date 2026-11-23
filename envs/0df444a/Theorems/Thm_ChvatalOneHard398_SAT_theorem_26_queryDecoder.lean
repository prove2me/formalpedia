-- Prove2me | Theorems.Thm_ChvatalOneHard398_SAT_theorem_26_queryDecoder
-- name    : ChvatalOneHard398.SAT.theorem_26_queryDecoder
-- status  : Open
-- author  : @Mr Robbins
-- created : 2026-11-23T03:28:18.530841+00:00
-- url     : https://prove2.me/theorems/909befe3-30b7-4df4-9187-6eabfac1bba5
-- title:
--   Theorem 26 — query decoder after lattice rounding
-- statement:
--   Assume a polynomial-time rounding map $f$ with exactly the correctness interface of Lemma 25: on a positive-dimensional nonsingular basis and $\nu>\sqrt n$, its output satisfies `RoundCorrect`. Construct the polynomial-time adaptive thin-query decoder of Theorem 26. Thus there is an oracle next-step algorithm $A$ and a fixed polynomial round bound such that $A$ runs for at most that many rounds on every input and oracle, every actual query is a `ConstructedQuery`, and for every BDD-promised input the final rational vector is a nearest lattice vector realizing $\operatorname{dist}(t,L(B))$ when the oracle is correct on `ThinQuery`. The construction must handle dimensions $n<150$ by a fixed bound, try $2^{2n},\ldots,2^{2n+n^2}$ in larger dimensions, recover all coefficients with binary queries, and return the selected lattice vector through `encOutput`. The statement explicitly assumes both polynomial time and correctness of the rounding map; Proposition 16 supplies the formulas and the imported binary-recovery invariant is the arithmetic basis of the bit queries.
-- source:
--   Alberto Del Pia, 0/1 integer programming over polytopes of Chvátal rank one is as hard as lattice problems, STOC 2027 submission #398 (October 2026), pp.27–29, Theorem 26 and its proof: the remaining oracle construction after the first sentence 'To solve BDD, we make the lattice integral (Lemma 25)'; Proposition 16 (pp.18–19,26–27) supplies the thin formulas and the induction on pp.28–29 supplies binary coordinate recovery; https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/398.pdf

import Mathlib
import Definitions.Def_ChvatalOneHard398_SAT_Oracle
import Definitions.Def_ChvatalOneHard398_SAT_Rounding
import Theorems.Thm_ChvatalOneHard398_SAT_theorem_26_bitRecovery

namespace ChvatalOneHard398.SAT

theorem theorem_26_queryDecoder
    (f : RoundInput → RoundData)
    (hf : PolyTime encRoundInput encRoundData f)
    (hf_correct : ∀ x, 0 < x.1.n → x.1.basis.det ≠ 0 →
      Real.sqrt x.1.n < (x.2 : ℝ) → RoundCorrect x (f x)) :
    ∃ (A : OracleAlg BDDInput Formula (List ℚ)) (rounds : Polynomial ℕ),
      IsPolyOracle encBDD encFormula encOutput A rounds ∧
      SolvesBDDWith A rounds ThinQuery ∧
      ∀ orc x, ∀ F ∈ (oracleRun A orc x (rounds.eval (encBDD x).length) []).queries,
        ConstructedQuery F := by sorry
