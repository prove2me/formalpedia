-- Prove2me | Theorems.Thm_DiazModulus_candidate_no_real_algebraic_line
-- name    : DiazModulus.candidate_no_real_algebraic_line
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-12T19:19:35.893976+00:00
-- url     : https://prove2.me/theorems/e561bb83-10d1-42d0-b2aa-1d5fb8d4a1d9
-- title:
--   A Diaz candidate lies on no real algebraic line
-- statement:
--   Let $u=x+iy\in\mathbb{C}$ be a **candidate** for Diaz's modulus conjecture: $u\neq 0$, $|u|$ algebraic over $\mathbb{Q}$, and $e^{u}$ algebraic over $\mathbb{Q}$.
--
--   Then $u$ lies on no affine line with real algebraic coefficients. Equivalently: for all $A,B,C\in\overline{\mathbb{Q}}\cap\mathbb{R}$ with $(A,B)\neq(0,0)$,
--
--   $$
--   Ax+By\neq C.
--   $$
--
--   The input is Hermite--Lindemann alone. A real algebraic line meets the circle $X^{2}+Y^{2}=|u|^{2}$ only in algebraic points (solve the linear equation for one coordinate and substitute; the resulting quadratic has non-zero leading coefficient $A^{2}+B^{2}$ because $A,B$ are real and not both zero). Hermite--Lindemann then makes $u$ transcendental, a contradiction.
--
--   This is the candidate-only "cheap" line exclusion, Remark 6.2 of Carlo Perassi's companion note to https://github.com/carlok/diaz-modulus-lean (version 1.9, 25 September 2026, GitHub release note-v1.9). The stronger statement `DiazModulus.no_algebraic_generalized_line` drops the modulus hypothesis at the cost of Baker's theorem on two logarithms; here the modulus hypothesis buys a proof that never mentions linear forms in logarithms.
-- source:
--   Carlo Perassi, companion note to https://github.com/carlok/diaz-modulus-lean, version 1.9, 25 September 2026 (GitHub release note-v1.9), Remark 6.2. Background: G. Diaz, J. Théor. Nombres Bordeaux 16 (2004), 535–553, §5.1.

import Mathlib
import Definitions.Def_DiazModulus

open Complex ComplexConjugate

namespace DiazModulus
theorem candidate_no_real_algebraic_line {u : ℂ} (h : IsCandidate u)
    {A B C : ℂ}
    (hA : IsAlgebraic ℚ A) (hB : IsAlgebraic ℚ B) (hC : IsAlgebraic ℚ C)
    (hAim : A.im = 0) (hBim : B.im = 0) (hCim : C.im = 0)
    (hne : ¬(A = 0 ∧ B = 0)) :
    A * ((u.re : ℝ) : ℂ) + B * ((u.im : ℝ) : ℂ) ≠ C := by sorry
end DiazModulus
