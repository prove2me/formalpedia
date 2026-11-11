-- Prove2me | Theorems.Thm_CorrBoundsPoly_ExactDegree_lemma_3_6
-- name    : CorrBoundsPoly.ExactDegree.lemma_3_6
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T15:58:55.35721+00:00
-- url     : https://prove2.me/theorems/3d4ddf45-faf0-482d-a6ee-3343374ddec3
-- title:
--   Lemma 3.6 — rational induction: $a_D(m)\le(3/2-1/(2D^2))(1-1/D^2)^m$ for dyadic $D$
-- statement:
--   For dyadic $D\ge1$ and every $m\ge0$,
--   $$a_D(m)\le C_D\,b_D^{\,m},\qquad C_D=\frac32-\frac1{2D^2},\quad b_D=1-\frac1{D^2}, \tag{3.9}$$
--   where for $D=1$ the convention $0^0=1$ is used. Here $a_D(m)=\nu(\sigma_{D,m})$ is the normalized rank defect of the elementary core (and $1$ when $m<D$).
--
--   This is the quantitative upper bound for the dyadic cores, giving $a_D(m)\le\frac32e^{-m/D^2}$ (Corollary 3.7).
--
--   Differences from the source:
--   - encoding: "dyadic $D\ge1$" → `IsDyadic D` ($D=2^a$, $a\ge0$); reason: every power of two is at least $1$; $0^0=1$ is Lean's convention, as on the page
-- source:
--   Xin Li, More on Correlation Bounds for Polynomials, STOC 2027 submission (manuscript sha256 aa4ef6f7…), p. 28 (PDF 30), Lemma 3.6, Eq. (3.9)

import Mathlib
import Definitions.Def_CorrBoundsPoly_ExactDegree_ElemSym

namespace CorrBoundsPoly.ExactDegree

/-- **Lemma 3.6** (Rational induction; Xin Li, *More on Correlation Bounds for Polynomials*, p. 28,
PDF 30). For dyadic `D ≥ 1` and every `m ≥ 0`, `a_D(m) ≤ C_D b_D^m` with
`C_D = 3/2 − 1/(2D²)`, `b_D = 1 − 1/D²` (Eq. (3.9)); for `D = 1`, `0^0 = 1`. -/
theorem lemma_3_6 (D : ℕ) (hD : IsDyadic D) (m : ℕ) :
    aD D m ≤ (3 / 2 - 1 / (2 * (D : ℝ) ^ 2)) * (1 - 1 / (D : ℝ) ^ 2) ^ m := by sorry

end CorrBoundsPoly.ExactDegree
