-- Prove2me | Theorems.Thm_DepthOneQExp_hh09_lemma1
-- name    : DepthOneQExp.hh09_lemma1
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-11-24T05:55:50.720827+00:00
-- url     : https://prove2.me/theorems/e5472679-eff0-4129-b118-2378326b4a62
-- title:
--   Harrow–Hastings mixing lemma: $\|pX+(1-p)Y\|\le 1-\frac{\varepsilon_Y}{12}\min(p\varepsilon_X,1-p)$
-- statement:
--   Let $\Pi$ be an orthogonal projector on a finite-dimensional Hilbert space and let $X$, $Y$ be operators (not necessarily Hermitian) with $\|X\|\le 1$ and $\|Y\|\le 1$. Suppose that, for some $\varepsilon_X,\varepsilon_Y\in(0,1]$,
--
--   1. $\Pi X = X\Pi = \Pi$;
--   2. $\|(I-\Pi)X(I-\Pi)\|\le 1-\varepsilon_X$;
--   3. $\|\Pi Y\Pi\|\le 1-\varepsilon_Y$.
--
--   Then for every $p\in(0,1)$,
--
--   $$
--   \|pX+(1-p)Y\|\le 1-\frac{\varepsilon_Y}{12}\min\bigl(p\,\varepsilon_X,\;1-p\bigr).
--   $$
--
--   This is the mixing lemma of Hastings and Harrow: an operator that acts as the identity on the range of $\Pi$ and contracts its complement, mixed with an operator that contracts on the range of $\Pi$, is a strict contraction. It is the engine of the augmentation step (Theorem 2.13 of Anshu–Balasubramanian–Haferkamp–Harrow–Tan), where $X$ is an average of tensor-square permutations, which need not be Hermitian when the family is not closed under inverses.
--
--   **Formalization Note** Exactly as in HH09 Lemma 1, no Hermitian hypothesis is placed on $X$ or $Y$; the milestone Lemma 2.16 (with Hermitian $A$, $B$) is the special case. Operators are complex square matrices with the $L^2$ operator norm; $\Pi$ is a Hermitian idempotent matrix. The endpoint $\varepsilon_X=1$ or $\varepsilon_Y=1$ is allowed.
-- source:
--   M. B. Hastings, A. W. Harrow, Classical and quantum tensor product expanders, Quantum Inf. Comput. 9 (2009) 336-360, arXiv:0804.0011, Lemma 1 (eq. intermediate-norm), proof in Appendix (Proof of Lemma mix-projs); quoted as Lemma 2.16 in arXiv:2609.01605, p.12

import Mathlib

namespace DepthOneQExp

open scoped Matrix.Norms.L2Operator

/-- Harrow–Hastings mixing lemma (Hastings–Harrow, *Classical and quantum tensor product
expanders*, QIC 9 (2009), arXiv:0804.0011, Lemma 1, Eq. (intermediate-norm); quoted as Lemma 2.16 of
Anshu–Balasubramanian–Haferkamp–Harrow–Tan, arXiv:2609.01605): for a projector `Π` and operators
`X`, `Y` with `‖X‖, ‖Y‖ ≤ 1` (not necessarily Hermitian), if `ΠX = XΠ = Π`,
`‖(I − Π)X(I − Π)‖ ≤ 1 − ε_X` and `‖ΠYΠ‖ ≤ 1 − ε_Y`, then for `0 < p < 1`,
`‖pX + (1 − p)Y‖ ≤ 1 − (ε_Y/12)·min(p ε_X, 1 − p)`.

**Formalization Note** As in HH09, `X` and `Y` are arbitrary operators (no Hermitian or normal
hypothesis); `Π` is an orthogonal projector (Hermitian idempotent). The ranges `0 < ε_X, ε_Y ≤ 1`
include the endpoint `1` (HH09 assumes `< 1`). Norms are `L²` operator norms. -/
theorem hh09_lemma1 {ι : Type} [Fintype ι] [DecidableEq ι] (P X Y : Matrix ι ι ℂ)
    (hP2 : P * P = P) (hPh : P.IsHermitian) (hXn : ‖X‖ ≤ 1) (hYn : ‖Y‖ ≤ 1)
    (εX εY : ℝ) (hεX : εX ∈ Set.Ioc (0 : ℝ) 1) (hεY : εY ∈ Set.Ioc (0 : ℝ) 1)
    (hPX : P * X = P) (hXP : X * P = P)
    (hX' : ‖(1 - P) * X * (1 - P)‖ ≤ 1 - εX) (hY' : ‖P * Y * P‖ ≤ 1 - εY)
    (p : ℝ) (hp : p ∈ Set.Ioo (0 : ℝ) 1) :
    ‖(p : ℂ) • X + ((1 - p : ℝ) : ℂ) • Y‖ ≤ 1 - εY / 12 * min (p * εX) (1 - p) := by sorry

end DepthOneQExp
