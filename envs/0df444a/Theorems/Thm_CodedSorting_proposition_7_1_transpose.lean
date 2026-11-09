-- Prove2me | Theorems.Thm_CodedSorting_proposition_7_1_transpose
-- name    : CodedSorting.proposition_7_1_transpose
-- status  : Open
-- author  : @iris
-- created : 2026-11-08T23:09:33.547611+00:00
-- url     : https://prove2.me/theorems/a146ce97-0acb-4c82-b423-3c10d4f0f2e8
-- title:
--   Proposition 7.1 (rearrangement part; companion: proposition_7_1_correctness) — $\pi$ and $\pi^{-1}$ are three adjacent field interchanges
-- statement:
--   Let $t\ge3$, $s=2^t$, $r=s^3=2^{3t}$, and split an index $j\in[2^{4t}]$ into four $t$-bit fields $(x_1,x_2,x_3,x_4)$ from highest to lowest. The transpose of step 2 of Columnsort,
--   $$\pi(j)=(j\bmod 2^t)\cdot2^{3t}+\lfloor j/2^t\rfloor,$$
--   which maps $(x_1,x_2,x_3,x_4)\mapsto(x_4,x_1,x_2,x_3)$, equals the composition of the address-field interchanges of width $t$ at positions $3,4$, then $2,3$, then $1,2$. The inverse of step 4, $\pi^{-1}(dr+q)=sq+d$, equals the same three interchanges in reverse order.
--
--   Each interchange is an address-field interchange of §6.1, so with Lemma 6.1 the two rearrangements of Columnsort cost six interchanges of width $t$.
--
--   Differences from the source:
--   - reading: Proposition 7.1's implementation sentence → the identities $\pi=$ three adjacent interchanges and $\pi^{-1}=$ the same three reversed, as maps on indices; correctness is the companion `proposition_7_1_correctness`; reason: this is the content the proof gives for "six address-field interchanges of width $t$"
--   - encoding: an adjacent field interchange → `interchangeIndex` of §6.1 with $G=1$, suffix $2^{t(2-i)}$ and the higher fields as prefix; reason: the record's own bits are the unchanged suffix coordinate (p.28)
-- source:
--   B. Li, Z. Li, S. Liu, Undirected Multiple-Unicast Network Coding and Faster External-Memory Integer Sorting, arXiv:2610.20079 (held version, sha256 6e149d97…8850b), Proposition 7.1, proof, "Implementing the rearrangements by address-field interchange", p.28 (PDF 29)

import Mathlib
import Definitions.Def_CodedSorting_Columnsort

namespace CodedSorting

/-- **Proposition 7.1 (The Columnsort reduction), the rearrangements as interchanges**, arXiv:2610.20079 (held version, sha256 6e149d97…8850b), p.28.

With `s = 2^t`, `r = s³ = 2^{3t}`, `t ≥ 3`, split a record index `j ∈ [2^{4t}]` into four `t`-bit fields
`(x₁, x₂, x₃, x₄)` from highest to lowest. The transpose of step 2, `π(j) = (j mod 2^t)·2^{3t} +
⌊j/2^t⌋`, equals the three adjacent address-field interchanges of width `t` at positions `3, 4`, then
`2, 3`, then `1, 2`; the inverse `π⁻¹` of step 4 equals the same three interchanges in reverse
order.

**Formalization Note.** `fieldSwapAdj t i` exchanges the fields at positions `i + 1`, `i + 2`
(`i : Fin 3`), as the §6.1 interchange `interchangeIndex` with `G = 1`. `transposeIdx` and
`transposeInvIdx` are the maps used by `columnsortLifted`. -/
theorem proposition_7_1_transpose (t : ℕ) (ht : 3 ≤ t) (j : ℕ) (hj : j < 2 ^ (4 * t)) :
    transposeIdx (2 ^ t) ((2 ^ t) ^ 3) j =
        fieldSwapAdj t 0 (fieldSwapAdj t 1 (fieldSwapAdj t 2 j)) ∧
      transposeInvIdx (2 ^ t) ((2 ^ t) ^ 3) j =
        fieldSwapAdj t 2 (fieldSwapAdj t 1 (fieldSwapAdj t 0 j)) := by sorry

end CodedSorting
