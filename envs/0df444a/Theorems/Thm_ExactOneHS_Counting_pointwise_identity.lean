-- Prove2me | Theorems.Thm_ExactOneHS_Counting_pointwise_identity
-- name    : ExactOneHS.Counting.pointwise_identity
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T05:13:03.188284+00:00
-- url     : https://prove2.me/theorems/34a175a3-9bc7-4c55-b21f-b71a26394af0
-- title:
--   §4.1, pointwise identity — $a_0(x) - a_1(x) = 1[H(x) = 1]$ for the path queries of Eq. (11)
-- statement:
--   Let $B$ be a CNF on $n$ declared variables, $h \ge 1$, and $\mathcal T_1, \dots, \mathcal T_h$ explicit term lists with DNF conditions $P_j$ and $H = B \wedge P_1 \wedge \dots \wedge P_h$. Let $Q_0, Q_1$ be the two-boundary path queries of Eq. (11), with endpoints $z_0 := 0$, $z_h := \beta$ substituted and tautological clauses deleted, and let $a_\beta(x)$ be the number of extensions of an original assignment $x \in \{0,1\}^n$ to the internal path variables $z_1, \dots, z_{h-1}$ that satisfy $Q_\beta$. Then for every $x \in \{0,1\}^n$,
--   $$a_0(x) - a_1(x) = \mathbf 1[H(x) = 1].$$
--
--   Summing over $x$ gives $\#\mathrm{SAT}(H) = \#\mathrm{SAT}(Q_0) - \#\mathrm{SAT}(Q_1)$, the counting identity (3) of Theorem 1.1.
--
--   **Formalization Note.** The identity is stated in $\mathbb Z$, with the indicator written as `if H x then 1 else 0`.
--
--   Differences from the source:
--   - encoding: B a CNF of width at most b and terms of at most d literals (the setting of Theorem 1.1) → B any CNF and terms any finite sets of literals, with no width parameters; reason: every finite CNF and every finite term list has such bounds b and d, so the instances are the same; the identity does not involve b or d
--   - encoding: declared variables x1, …, xn, z1, …, z(h−1) and edges j = 1, …, h → Fin (n + (h − 1)) with x first (indices 0..n−1) and z_k at index n + k − 1; edge j is e = j − 1 in Fin h; reason: Lean convention; for h ≥ 1, n + (h − 1) = n + h − 1
--   - encoding: "substitute the endpoint constants and delete tautological clauses" → a clause with a true constant literal, or with a literal and its negation, is deleted; false constant literals are dropped; clauses of B are kept as they are; reason: the page does not say whether B's own clauses are simplified; deleting or keeping a tautological clause does not change any count
--   - encoding: a0(x) − a1(x) = 1[H(x) = 1] → the difference in ℤ equals if H x = true then 1 else 0; reason: avoids truncated natural subtraction
-- source:
--   Chen, Jiang, Zhu, Counting Exact-One Hitting Sets in Subexponential Time, STOC 2027 submission (manuscript sha256 4b9a238a…), p. 12, §4.1, proof of Theorem 1.1, pointwise identity

import Mathlib
import Definitions.Def_SubexponentialSAT
import Definitions.Def_ExactOneHS_Counting_DNFCondition
import Definitions.Def_ExactOneHS_Counting_PathQuery

namespace ExactOneHS.Counting

/-- **§4.1, pointwise identity.** For a CNF `B` on `n` declared variables and `h ≥ 1` explicit
term lists, the path queries `Q_0, Q_1` of Eq. (11) satisfy, for every original assignment `x`,
`a_0(x) − a_1(x) = 1[H(x) = 1]`, where `a_β(x)` is the number of extensions of `x` to the internal
path variables `z_1, …, z_{h-1}` satisfying `Q_β`. -/
theorem pointwise_identity (P : TwoBoundaryInput) (hP : 1 ≤ P.h) (x : Fin P.n → Bool) :
    (P.extensionCount false x : ℤ) - (P.extensionCount true x : ℤ) =
      if P.H x = true then 1 else 0 := by sorry

end ExactOneHS.Counting
