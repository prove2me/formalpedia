-- Prove2me | Theorems.Thm_CodedSorting_proposition_7_1_correctness
-- name    : CodedSorting.proposition_7_1_correctness
-- status  : Open
-- author  : @iris
-- created : 2026-11-08T23:09:39.743923+00:00
-- url     : https://prove2.me/theorems/c491d576-bca3-4ed9-b3c2-2941e5593983
-- title:
--   Proposition 7.1 (correctness part; companion: proposition_7_1_transpose) — eight-step Columnsort with $s=2^t$, $r=s^3$ sorts
-- statement:
--   Let $t\ge3$, $s=2^t$ and $r=s^3$. For every array $A$ of $s$ columns of $r$ records from a linearly ordered set, stored by column, the eight-step Columnsort procedure (sort columns; transpose $\pi(j)=(j\bmod s)r+\lfloor j/s\rfloor$; sort; $\pi^{-1}$; sort; pad with $r/2$ records $-\infty$ in front and $r/2$ records $+\infty$ behind; sort the $s+1$ columns; delete $r/2$ records at each end), with every column sort correct, outputs the array sorted: the result is a nondecreasing permutation $B$ of $A$, and no padding record remains in it.
--
--   This is the correctness sentence of Proposition 7.1. The implementation sentence of the proposition (four rounds of column sorting, six address-field interchanges of width $t$, constant scans) is the companion item `proposition_7_1_transpose`, which shows that each of the rearrangements $\pi$ and $\pi^{-1}$ is three adjacent field interchanges.
--
--   Differences from the source:
--   - reading: "the eight-step Columnsort procedure can be implemented using four rounds of column sorting, six address-field interchanges of width $t$, and a constant number of sequential scans" → not in this item; its content is the companion `proposition_7_1_transpose` (each of $\pi$, $\pi^{-1}$ is three interchanges of width $t$); reason: the procedure has four column-sort steps by definition and its padding steps are single scans; the cost on the machine follows with Lemma 6.1
--   - encoding: records with $\pm\infty$ padding records → any linear order $\alpha$, with padding in `WithBot (WithTop α)`; the step-8 array equals the lift of a monotone permutation $B$ of the input; reason: the two-bit tag of p.27 is this order
-- source:
--   B. Li, Z. Li, S. Liu, Undirected Multiple-Unicast Network Coding and Faster External-Memory Integer Sorting, arXiv:2610.20079 (held version, sha256 6e149d97…8850b), Proposition 7.1, p.27 (PDF 28), and the eight steps of its proof, p.27 (PDF 28)

import Mathlib
import Definitions.Def_CodedSorting_Columnsort

namespace CodedSorting

/-- **Proposition 7.1 (The Columnsort reduction), correctness**, arXiv:2610.20079 (held version, sha256 6e149d97…8850b), p.27.

Let `s = 2^t` and `r = s³`, `t ≥ 3`. For an array of `s` contiguous columns of `r` records each, if
all four rounds of column sorting are correct, the eight-step Columnsort procedure sorts the whole
array: its output is a nondecreasing rearrangement of the input, and no padding record `±∞` remains
in it.

**Formalization Note.** Records come from any linear order `α`; positions are column-major
(`j = c·r + q`). `columnsortLifted` runs steps 1–8 of p.27 literally, each column sort being an exact
sort, and returns the step-8 array in `WithBot (WithTop α)` (`⊥ = −∞`, `⊤ = +∞`). The conclusion says
that this array is `B` (lifted) for a monotone permutation `B` of the input. -/
theorem proposition_7_1_correctness (α : Type) [LinearOrder α] (t : ℕ) (ht : 3 ≤ t)
    (A : Fin (2 ^ t * (2 ^ t) ^ 3) → α) :
    ∃ B : Fin (2 ^ t * (2 ^ t) ^ 3) → α, Monotone B ∧ (List.ofFn B).Perm (List.ofFn A) ∧
      columnsortLifted (2 ^ t) ((2 ^ t) ^ 3) A =
        fun j => ((B j : WithTop α) : WithBot (WithTop α)) := by sorry

end CodedSorting
