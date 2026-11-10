-- Prove2me | Theorems.Thm_ExactOneHS_Counting_eq_17
-- name    : ExactOneHS.Counting.eq_17
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T05:12:14.043021+00:00
-- url     : https://prove2.me/theorems/635459f2-ea20-449d-9328-290e480905b0
-- title:
--   Eq. (17) — exclusion and coverage: $Z(U,F) = \#\mathrm{SAT}(B \wedge C_1 \wedge \dots \wedge C_h)$ for an augmented row basis
-- statement:
--   Let $([r], F)$ be an Exact-One Hitting Set instance that is not one of the direct cases ($r \ge 2$, $F$ nonempty, $\emptyset \notin F$, $Ax = \mathbf 1$ consistent over $\mathbb Q$, and $\operatorname{rank} A < r$), with incidence matrix $A$. Let $S_1, \dots, S_h$ be original sets of $F$ whose rows form a basis of the row space of the augmented matrix $(A \mid \mathbf 1)$, so that they have the same Boolean solutions as $F$. With the pairwise exclusions $B$ and coverage clauses $C_j$ of Eq. (16) built from $S_1, \dots, S_h$,
--   $$Z(U, F) = \#\mathrm{SAT}(B \wedge C_1 \wedge \dots \wedge C_h),$$
--   where the formula retains all $r$ original variable declarations.
--
--   This identity turns the exact-one count into a model count of a CNF with $O(r^2)$ binary clauses and $h$ wide clauses, to which the wide-clause specialization (Lemma 4.1) applies.
--
--   **Formalization Note.** The retained sets are given by a set $s$ of row indices with the basis property; $h = |s|$; the count is over all assignments `Fin r → Bool`.
--
--   Differences from the source:
--   - reading: "By Lemma 3.1, a basis of the augmented row space selects exactly h original sets S1, …, Sh" → any index set s whose rows of (A | 1) are linearly independent and span the row space of (A | 1); reason: the page specifies the retained sets only as a basis of the augmented row space; the identity is stated for every such basis, which includes the one Lemma 3.1 selects
--   - encoding: unordered pairs {u, v} ∈ E and the formula B ∧ C1 ∧ ⋯ ∧ Ch → pairs (u, v) with u < v in Fin r; the formula is a Finset of clauses (exclusionCoverage), so repeated clauses collapse; reason: same pairs; a conjunction is unchanged by repeating a conjunct
--   - encoding: U = [r], F a family with repetitions, #SAT over all r declared variables → Fin r (0-based), F a List, count over all Fin r → Bool; reason: Lean convention; same instances
-- source:
--   Chen, Jiang, Zhu, Counting Exact-One Hitting Sets in Subexponential Time, STOC 2027 submission (manuscript sha256 4b9a238a…), p. 15, proof of Theorem 1.2, Eqs. (16), (17)

import Mathlib
import Definitions.Def_SubexponentialSAT
import Definitions.Def_ExactOneHS_Counting_Instance
import Definitions.Def_ExactOneHS_Counting_ExclusionCoverage

namespace ExactOneHS.Counting

open OAI.Algorithms.SubexponentialSAT

/-- **Eq. (17).** For an Exact-One Hitting Set instance outside the direct cases of Theorem 1.2,
and original sets `S_1, …, S_h` whose rows form a basis of the row space of the augmented matrix
`(A | 1)`, the number of exact-one hitting sets equals the model count, over all `r` declared
variables, of `B ∧ C_1 ∧ ⋯ ∧ C_h` (pairwise exclusions `B` and coverage clauses `C_j` of Eq. (16)
built from the retained sets). -/
theorem eq_17 (I : Instance) (hI : ¬ I.IsDirectCase) (s : Finset (Fin I.family.length))
    (hs : I.IsAugmentedRowBasis s) :
    I.Z = SAT.count (exclusionCoverage (I.retained s)) := by sorry

end ExactOneHS.Counting
