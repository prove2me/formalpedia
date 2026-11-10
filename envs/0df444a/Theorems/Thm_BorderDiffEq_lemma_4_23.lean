-- Prove2me | Theorems.Thm_BorderDiffEq_lemma_4_23
-- name    : BorderDiffEq.lemma_4_23
-- status  : Open
-- author  : @iris
-- created : 2026-11-09T22:26:24.676385+00:00
-- url     : https://prove2.me/theorems/b3c659e9-a680-4f99-b1c1-39eb9cf0b3b4
-- title:
--   Lemma 4.23 — the signed maximal minors of an $n\times(n+1)$ matrix form a kernel vector
-- statement:
--   Let $A$ be an $n\times(n+1)$ matrix over a commutative ring and let $A_j$ be the $n\times n$ matrix obtained by removing the $j$-th column. Define $v\in R^{n+1}$ by $v_j=(-1)^{j+1}\det(A_j)$ ($1\le j\le n+1$). Then
--   $$
--   Av=0 .
--   $$
--   Applied to the matrix $(D^jS_i)$ this yields the paper's differential equation (Lemma 5.1).
--
--   **Formalization Note** With 0-based columns, $v$ is `signedMinor A`, $v_j=(-1)^j\det(A\text{ without column } j)$.
--
--   Differences from the source:
--   - generalization: $A\in F^{n\times(n+1)}$ of rank $n$ over a field $F$ → any $n\times(n+1)$ matrix over any commutative ring; reason: the identity holds for every matrix; the source's matrices are instances
--   - encoding: 1-based $j$, $v_j=(-1)^{j+1}\det(A_j)$ → 0-based $j$, $v_j=(-1)^j\det(A_j)$; reason: same vector after the index shift $j'=j+1$
-- source:
--   Bhat–Dutta–Kaplan–Shpilka–Shringi, Demystifying Border of Structured Algebraic Circuits via Differential Equations, manuscript (STOC 2027 submission; preprint basis, sha256 583bcc89e7078b50ae14babedf540a37b37e36912abda1931e4aaeb64bc57db8), Lemma 4.23, p.30

import Mathlib
import Definitions.Def_BorderDiffEq_signedMinor

namespace BorderDiffEq

/-- **Lemma 4.23 (signed maximal minors give a kernel vector)** (Bhat–Dutta–Kaplan–Shpilka–Shringi,
*Demystifying Border of Structured Algebraic Circuits via Differential Equations*, manuscript (STOC
2027 submission), Lemma 4.23, p.30). Let `A` be an `n × (n+1)` matrix and `A_j` the `n × n` matrix
obtained by removing the `j`-th column. For `v_j := (-1)^{j+1} det(A_j)` (1-based `j`), `A v = 0`.

**Formalization Note.** Entries in any commutative ring `R` (the paper: a field `F`). Columns are
0-based, so `v = signedMinor A` with `v_j = (-1)^j det(A with column j removed)`, which is the
paper's sign `(-1)^{j'+1}` for `j' = j + 1`. The hypothesis "of rank `n`" is dropped: the identity
holds for every matrix. -/
theorem lemma_4_23 (R : Type) [CommRing R] (n : ℕ) (A : Matrix (Fin n) (Fin (n + 1)) R) :
    A.mulVec (signedMinor A) = 0 := by sorry

end BorderDiffEq
