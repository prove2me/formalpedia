-- Prove2me | Theorems.Thm_ExactOneHS_Counting_lemma_4_1
-- name    : ExactOneHS.Counting.lemma_4_1
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T05:11:29.7432+00:00
-- url     : https://prove2.me/theorems/55953b18-ea0e-4cba-8283-92c6fc76fb81
-- title:
--   Lemma 4.1 — wide-clause specialization: a 3-CNF and $h \ge 1$ wide clauses give two 3-CNF queries on $n + h - 1$ variables
-- statement:
--   Let $B$ be a 3-CNF (every clause has at most three literals) with $m_B$ clauses on $n$ declared variables, and let $C_1, \dots, C_h$ be clauses of arbitrary width on those variables, with literals of either sign. **Lemma 4.1** asserts that for $h \ge 1$ there are two ordinary 3-CNFs $Q_0, Q_1$, each with exactly $n + h - 1$ declared variables and at most $m_B + 2\sum_j |C_j|$ clauses, such that
--   $$\#\mathrm{SAT}(B \wedge C_1 \wedge \dots \wedge C_h) = \#\mathrm{SAT}(Q_0) - \#\mathrm{SAT}(Q_1).$$
--
--   This is the case of Theorem 1.1 with one-literal terms, $b = 3$ and $d = 1$, and is the form used for Exact-One Hitting Set.
--
--   **Formalization Note.** The queries are CNFs over `Fin (n + h - 1)`, which for $h \ge 1$ has exactly $n + h - 1$ elements; the identity is in $\mathbb Z$.
--
--   Differences from the source:
--   - encoding: declared variables, the formula B ∧ C1 ∧ ⋯ ∧ Ch, mB, |Cj| → Fin n and Fin (n + h − 1); the CNF B ∪ {C1, …, Ch} (a Finset of clauses); B.card; (C j).card; identity in ℤ; reason: Lean convention; a conjunction is unchanged by repeating a conjunct, and h ≥ 1 makes n + h − 1 exact
-- source:
--   Chen, Jiang, Zhu, Counting Exact-One Hitting Sets in Subexponential Time, STOC 2027 submission (manuscript sha256 4b9a238a…), p. 13, Lemma 4.1, Eq. (13)

import Mathlib
import Definitions.Def_SubexponentialSAT

namespace ExactOneHS.Counting

open OAI.Algorithms.SubexponentialSAT

/-- **Lemma 4.1 (Wide-clause specialization).** Let `B` be a 3-CNF on `n` declared variables and
`C_1, …, C_h` (`h ≥ 1`) clauses of arbitrary width on those variables, with literals of either
sign. Then there are two ordinary 3-CNFs `Q_0, Q_1`, each on exactly `n + h − 1` declared
variables and with at most `m_B + 2 ∑_j |C_j|` clauses, such that
`#SAT(B ∧ C_1 ∧ ⋯ ∧ C_h) = #SAT(Q_0) − #SAT(Q_1)`. -/
theorem lemma_4_1 (n : ℕ) (B : SAT.CNF (Fin n)) (hB : SAT.WidthAtMost 3 B) (h : ℕ) (hh : 1 ≤ h)
    (C : Fin h → SAT.Clause (Fin n)) :
    ∃ Q0 Q1 : SAT.CNF (Fin (n + h - 1)),
      SAT.WidthAtMost 3 Q0 ∧ SAT.WidthAtMost 3 Q1 ∧
      Q0.card ≤ B.card + 2 * ∑ j, (C j).card ∧
      Q1.card ≤ B.card + 2 * ∑ j, (C j).card ∧
      (SAT.count (B ∪ Finset.univ.image C) : ℤ) = (SAT.count Q0 : ℤ) - (SAT.count Q1 : ℤ) := by sorry

end ExactOneHS.Counting
