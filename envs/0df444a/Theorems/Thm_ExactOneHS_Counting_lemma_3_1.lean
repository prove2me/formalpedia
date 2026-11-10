-- Prove2me | Theorems.Thm_ExactOneHS_Counting_lemma_3_1
-- name    : ExactOneHS.Counting.lemma_3_1
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T05:12:25.555852+00:00
-- url     : https://prove2.me/theorems/c8fdfc90-c9eb-42cf-8d23-1d672ada4c07
-- title:
--   Lemma 3.1 — row selection: at most $r+1$ original equations with the same rational solutions, exactly $\operatorname{rank} A$ if consistent, in polynomial bit time
-- statement:
--   Let $Ax = b$ be an explicitly represented rational system with $m$ equations in $r$ variables. **Lemma 3.1** (row selection, after Jansen and Pieterse) asserts that one can select, deterministically in polynomial bit time, a set $s$ of original equations such that
--   $$|s| \le r + 1, \qquad \{x \in \mathbb{Q}^r : a_i \cdot x = b_i \ \forall i \in s\} = \{x \in \mathbb{Q}^r : Ax = b\},$$
--   and $|s| = \operatorname{rank} A$ whenever the system is consistent. Since the selected equations have the same rational solutions, they have in particular the same Boolean solutions; applied to an exact-one system $Ax = \mathbf 1$, the selected equations are original input sets.
--
--   Formally: there is a selection map $s(\cdot)$ from systems to sets of equation indices, computed on the binary codes of the systems by a single polynomial-time machine, such that for every system the three properties above hold.
--
--   The lemma is the first step of the Exact-One Hitting Set reduction: it reduces an arbitrary number of exact-one constraints to at most $\operatorname{rank} A \le r$ of the original ones.
--
--   **Formalization Note.** Polynomial time is `PPSLattice.PolyTimeOn`: one Mathlib `TM2` multi-stack machine, running in time polynomial in the length of the input code, maps the code of every system to the code of the selected index set.
--
--   Differences from the source:
--   - encoding: an explicitly represented rational system Ax = b and the selected original equations → a RationalSystem coded by encodeSystem (r in unary, each equation's r + 1 coefficients as binary rationals encRat); the selection is a Finset (Fin m) of 0-based row indices, output as an increasing list of unary indices; reason: the paper fixes no format; rationals are written in binary as bit complexity requires, and r in unary adds at most one bit per listed coefficient
--   - encoding: deterministic polynomial bit time → PPSLattice.PolyTimeOn: one Mathlib TM2 machine, time polynomial in the length of the input code, maps the code of every system to the code of the selection; reason: standard machine model for polynomial time on bit strings
--   - reading: if the system is consistent, exactly rank(A) rows suffice → the same selection has exactly A.rank rows whenever the system is consistent; reason: the proof selects a basis of the augmented row space, whose size is rank(A | b) = rank(A) in the consistent case, and the proof of Theorem 1.2 uses that the selection has exactly h = rank(A) rows; this is the stronger of the two readings
--   - encoding: the same rational, and hence Boolean, solutions → the same rational solutions x : Fin r → ℚ; reason: Boolean solutions are the 0/1 points among the rational ones, so they follow
-- source:
--   Chen, Jiang, Zhu, Counting Exact-One Hitting Sets in Subexponential Time, STOC 2027 submission (manuscript sha256 4b9a238a…), p. 10, Lemma 3.1

import Mathlib
import Definitions.Def_PPSLattice_PolyTimeOn
import Definitions.Def_ExactOneHS_Counting_RationalSystem

namespace ExactOneHS.Counting

/-- **Lemma 3.1 (Row selection; Jansen–Pieterse).** There is a deterministic polynomial-time
procedure (one polynomial-time machine on the binary codes) that, for every explicitly
represented rational system `A x = b` in `r` variables, selects a set of at most `r + 1` original
equations whose rational solutions are exactly those of the whole system, and that selects exactly
`rank A` equations whenever the system is consistent. -/
theorem lemma_3_1 :
    ∃ select : (S : RationalSystem) → Finset (Fin S.m),
      PPSLattice.PolyTimeOn encodeSystem (fun S => encodeRowSet (select S)) ∧
      ∀ S : RationalSystem,
        (select S).card ≤ S.r + 1 ∧
        (∀ x : Fin S.r → ℚ, S.SatisfiesRows (select S) x ↔ S.IsSolution x) ∧
        (S.IsConsistent → (select S).card = S.A.rank) := by sorry

end ExactOneHS.Counting
