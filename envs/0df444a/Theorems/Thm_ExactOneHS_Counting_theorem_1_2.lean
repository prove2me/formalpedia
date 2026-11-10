-- Prove2me | Theorems.Thm_ExactOneHS_Counting_theorem_1_2
-- name    : ExactOneHS.Counting.theorem_1_2
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T05:12:12.563207+00:00
-- url     : https://prove2.me/theorems/cb9f7c7a-2bdc-4345-b9a8-74ce6bfae496
-- title:
--   Theorem 1.2 — Exact-One Hitting Set counting reduction: $Z(U,F) = \#\mathrm{SAT}(Q_0) - \#\mathrm{SAT}(Q_1)$ with two 3-CNFs on $r + \operatorname{rank} A - 1 \le 2r - 2$ variables, $O(r^2)$ clauses
-- statement:
--   Let $([r], F)$ be an Exact-One Hitting Set instance with count $Z(U, F)$ and rational incidence matrix $A$, and let $h = \operatorname{rank} A$ over $\mathbb Q$. **Theorem 1.2** asserts that there is a polynomial-time procedure for Exact-One Hitting Set on $r$ declared elements that computes $Z(U, F)$ directly if $r \le 1$, if $F$ is empty or contains an empty set, or if the system $Ax = \mathbf 1$ is inconsistent over $\mathbb Q$ or has full column rank; and in every remaining case constructs two ordinary unweighted 3-CNFs $Q_0, Q_1$, nonadaptively, with
--   $$Z(U, F) = \#\mathrm{SAT}(Q_0) - \#\mathrm{SAT}(Q_1),$$
--   each with exactly $r + h - 1 \le 2r - 2$ declared variables and $O(r^2)$ clauses, regardless of the number and sizes of the input sets.
--
--   Formally: there are a constant $C$ and a procedure, computed on bit-string codes by a single polynomial-time machine, such that for every instance: in a direct case the output is the number $Z(U, F)$; otherwise the output is a query pair $(N, Q_0, Q_1)$ with $N = r + \operatorname{rank} A - 1$, $N \le 2r - 2$, both queries of width at most $3$ and with at most $C r^2$ clauses, and $Z(U, F) = \#\mathrm{SAT}(Q_0) - \#\mathrm{SAT}(Q_1)$ in $\mathbb Z$. Since the two kinds of output differ, the procedure returns the number $Z(U,F)$ exactly in the direct cases.
--
--   The theorem reduces exact counting of exact-one hitting sets with $r$ elements to two counting queries on fixed-width CNFs with at most $2r - 2$ variables, so that any fixed-width model counter whose running time is governed by the number of variables applies.
--
--   **Formalization Note.** Polynomial time is `PPSLattice.PolyTimeOn` on the codes `encodeInstance` ($r$ in unary, element indices in unary) and `encodeOutput` (a directly computed count in binary, or both queries written out by `encodeCNF`). The constant $C$ is fixed before the procedure and the instance.
--
--   Differences from the source:
--   - encoding: instances ([r], F) with U = [r] and F an explicit family that may repeat sets → Instance with elements Fin r (0-based) and family a List (Finset (Fin r)); A has one row per listed set; reason: Lean convention; same instances
--   - encoding: "a polynomial-time procedure" with input length L and r = O(L) → proc : Instance → Output with PPSLattice.PolyTimeOn encodeInstance (r in unary, sets as increasing unary index lists) and encodeOutput (tag bit, count in binary least significant bit first, or encodeCNF Q0 ++ encodeCNF Q1); reason: the paper's convention that the instance declares [r] explicitly (r = O(L)); the direct answer can be 2^r and is written in binary
--   - encoding: computes Z directly in the listed cases, constructs two queries in every remaining case → (IsDirectCase I → proc I = direct (Z I)) ∧ (¬ IsDirectCase I → proc I = queries q with the stated properties); reason: the two output kinds are distinct, so this says the output is Z itself exactly in the direct cases
--   - encoding: "nonadaptively" → both queries are components of one output value; reason: neither query can depend on the other's count
--   - encoding: exactly r + h − 1 ≤ 2r − 2 variables, h = rank(A) → (N : ℤ) = r + rank A − 1 and (N : ℤ) ≤ 2r − 2, with rank the Matrix.rank over ℚ of the full incidence matrix; reason: integer arithmetic avoids truncated subtraction
--   - encoding: O(r²) clauses → ∃ C : ℕ before the procedure and every instance, each query has card ≤ C · r²; reason: an absolute constant, uniform over instances (r ≥ 2 in the remaining case)
--   - encoding: ordinary unweighted 3-CNFs, Z = #SAT(Q0) − #SAT(Q1) → SAT.CNF (Fin N) with WidthAtMost 3, SAT.count over all Fin N → Bool, identity in ℤ; reason: Lean convention; ℤ avoids truncated subtraction
-- source:
--   Chen, Jiang, Zhu, Counting Exact-One Hitting Sets in Subexponential Time, STOC 2027 submission (manuscript sha256 4b9a238a…), p. 5, Theorem 1.2, Eq. (5); proved on p. 15, §5.1

import Mathlib
import Definitions.Def_SubexponentialSAT
import Definitions.Def_PPSLattice_PolyTimeOn
import Definitions.Def_ExactOneHS_Counting_Instance
import Definitions.Def_ExactOneHS_Counting_Output

namespace ExactOneHS.Counting

open OAI.Algorithms.SubexponentialSAT

/-- **Theorem 1.2 (Counting reduction for Exact-One Hitting Set).** There are a constant `C` and
a polynomial-time procedure on Exact-One Hitting Set instances `([r], F)` that returns `Z(U, F)`
itself in the direct cases (`r ≤ 1`, `F` empty, `∅ ∈ F`, `A x = 1` inconsistent over `ℚ`, or
`rank A = r`), and in every remaining case returns two ordinary 3-CNFs `Q_0, Q_1` on exactly
`r + rank A − 1 ≤ 2r − 2` declared variables, each with at most `C · r²` clauses, such that
`Z(U, F) = #SAT(Q_0) − #SAT(Q_1)`. -/
theorem theorem_1_2 :
    ∃ C : ℕ, ∃ proc : Instance → Output,
      PPSLattice.PolyTimeOn encodeInstance (fun I => encodeOutput (proc I)) ∧
      ∀ I : Instance,
        (I.IsDirectCase → proc I = Output.direct I.Z) ∧
        (¬ I.IsDirectCase → ∃ q : QueryPair, proc I = Output.queries q ∧
          (q.N : ℤ) = (I.r : ℤ) + (I.incidence.rank : ℤ) - 1 ∧
          (q.N : ℤ) ≤ 2 * (I.r : ℤ) - 2 ∧
          SAT.WidthAtMost 3 q.Q0 ∧ SAT.WidthAtMost 3 q.Q1 ∧
          q.Q0.card ≤ C * I.r ^ 2 ∧ q.Q1.card ≤ C * I.r ^ 2 ∧
          (I.Z : ℤ) = (SAT.count q.Q0 : ℤ) - (SAT.count q.Q1 : ℤ)) := by sorry

end ExactOneHS.Counting
