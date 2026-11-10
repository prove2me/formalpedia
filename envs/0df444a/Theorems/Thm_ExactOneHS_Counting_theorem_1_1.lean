-- Prove2me | Theorems.Thm_ExactOneHS_Counting_theorem_1_1
-- name    : ExactOneHS.Counting.theorem_1_1
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T05:12:11.285202+00:00
-- url     : https://prove2.me/theorems/01315038-03c9-4c63-97b9-95cf339db1e3
-- title:
--   Theorem 1.1 — two-boundary counting reduction: $\#\mathrm{SAT}(H) = \#\mathrm{SAT}(Q_0) - \#\mathrm{SAT}(Q_1)$, $N = n + h - 1$, width $\le \max\{b, d+2\}$, $\le m_B + 2\sum_j |T_j|$ clauses
-- statement:
--   Let $B$ be a CNF of width at most $b$ with $m_B$ clauses on $n$ declared variables, and for $j \in [h]$ let
--   $$P_j(x) := \bigvee_{T \in \mathcal T_j} \bigwedge_{\ell \in T} \ell, \qquad H := B \wedge \bigwedge_{j=1}^{h} P_j,$$
--   where every term has at most $d$ literals and all term lists $\mathcal T_j$ are explicit. **Theorem 1.1** asserts: if $h \ge 1$, one can construct in polynomial time two ordinary unweighted CNFs $Q_0, Q_1$ with
--   $$\#\mathrm{SAT}(H) = \#\mathrm{SAT}(Q_0) - \#\mathrm{SAT}(Q_1),$$
--   whose common number of declared variables $N$, clause widths $K_\beta$ and clause counts $M_\beta$ satisfy
--   $$N = n + h - 1, \qquad K_\beta \le \max\{b, d + 2\}, \qquad M_\beta \le m_B + 2 \sum_{j=1}^{h} |\mathcal T_j|.$$
--   For $h = 0$, one query to $B$ suffices: $\#\mathrm{SAT}(H) = \#\mathrm{SAT}(B)$.
--
--   Formally: there is one construction, computed on bit-string codes by a single polynomial-time machine, that maps every input $(n, B, h, \mathcal T_1, \dots, \mathcal T_h)$ to a query pair; for every input with $h \ge 1$ the pair has $N = n + h - 1$ variables, satisfies the identity in $\mathbb Z$, has at most $m_B + 2\sum_j |\mathcal T_j|$ clauses in each query, and, for all $b, d$ such that $B$ has width at most $b$ and every term at most $d$ literals, both queries have width at most $\max\{b, d+2\}$; and for every input with $h = 0$, $\#\mathrm{SAT}(H) = \#\mathrm{SAT}(B)$.
--
--   The theorem makes the number of auxiliary variables depend only on the number $h$ of conditions, not on their number of terms or literals.
--
--   **Formalization Note.** Polynomial time is `PPSLattice.PolyTimeOn` on the codes `encodeTwoBoundaryInput` and `encodeQueryPair`.
--
--   Differences from the source:
--   - encoding: "one can construct in polynomial time" → one map construct : TwoBoundaryInput → QueryPair with PPSLattice.PolyTimeOn on encodeTwoBoundaryInput (n, h and literal codes in unary) and encodeQueryPair (encodeCNF of both queries); reason: standard machine model; unary n and h are dominated by the length of the explicit input, which declares the variables
--   - encoding: N = n + h − 1 → N + 1 = n + h (for h ≥ 1); reason: avoids truncated natural subtraction; equal for h ≥ 1
--   - encoding: B of width at most b, every term of at most d literals, Kβ ≤ max{b, d + 2} → for all b d, if WidthAtMost b B and every listed term has card ≤ d then both queries have WidthAtMost (max b (d + 2)); reason: b and d are bounds of the input, not inputs of the construction; quantifying over them after the construction is the same statement
--   - encoding: mB clauses, |Tj| terms, #SAT(H) = #SAT(Q0) − #SAT(Q1) → B.card (a CNF is a Finset of clauses), (terms j).length (term lists are Lists, repetitions counted), identity in ℤ; reason: Lean convention; the identity in ℤ avoids truncated subtraction
--   - reading: "For h = 0, one query to B suffices" → if h = 0 then #SAT(H) = #SAT(B); reason: with no conditions H is B, so the single query is B itself
-- source:
--   Chen, Jiang, Zhu, Counting Exact-One Hitting Sets in Subexponential Time, STOC 2027 submission (manuscript sha256 4b9a238a…), pp. 4–5, Theorem 1.1, Eqs. (3), (4)

import Mathlib
import Definitions.Def_SubexponentialSAT
import Definitions.Def_PPSLattice_PolyTimeOn
import Definitions.Def_ExactOneHS_Counting_DNFCondition
import Definitions.Def_ExactOneHS_Counting_Output

namespace ExactOneHS.Counting

open OAI.Algorithms.SubexponentialSAT

/-- **Theorem 1.1 (Two-boundary counting reduction).** There is a polynomial-time construction
that maps a CNF `B` on `n` declared variables and `h` explicit term lists `T_1, …, T_h` to two
ordinary CNFs `Q_0, Q_1` on a common number `N` of declared variables such that, if `h ≥ 1`:
`N = n + h − 1`; `#SAT(H) = #SAT(Q_0) − #SAT(Q_1)` in `ℤ` with `H = B ∧ ⋀_j P_j`; whenever `B` has
width at most `b` and every term at most `d` literals, both queries have width at most
`max {b, d + 2}`; and each query has at most `m_B + 2 ∑_j |T_j|` clauses. For `h = 0`,
`#SAT(H) = #SAT(B)`. -/
theorem theorem_1_1 :
    ∃ construct : TwoBoundaryInput → QueryPair,
      PPSLattice.PolyTimeOn encodeTwoBoundaryInput (fun P => encodeQueryPair (construct P)) ∧
      ∀ P : TwoBoundaryInput,
        (1 ≤ P.h →
          (construct P).N + 1 = P.n + P.h ∧
          (P.countH : ℤ) = (SAT.count (construct P).Q0 : ℤ) - (SAT.count (construct P).Q1 : ℤ) ∧
          (∀ b d : ℕ, SAT.WidthAtMost b P.B → (∀ j, ∀ T ∈ P.terms j, T.card ≤ d) →
            SAT.WidthAtMost (max b (d + 2)) (construct P).Q0 ∧
            SAT.WidthAtMost (max b (d + 2)) (construct P).Q1) ∧
          (construct P).Q0.card ≤ P.B.card + 2 * P.totalTerms ∧
          (construct P).Q1.card ≤ P.B.card + 2 * P.totalTerms) ∧
        (P.h = 0 → P.countH = SAT.count P.B) := by sorry

end ExactOneHS.Counting
