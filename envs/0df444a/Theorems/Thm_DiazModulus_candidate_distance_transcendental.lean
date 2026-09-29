-- Prove2me | Theorems.Thm_DiazModulus_candidate_distance_transcendental
-- name    : DiazModulus.candidate_distance_transcendental
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-12T20:02:52.065797+00:00
-- url     : https://prove2.me/theorems/2ccd6ba0-97b2-4e09-8a47-2102927ddcf9
-- title:
--   Distance from a Diaz candidate to a non-zero algebraic point is transcendental
-- statement:
--   Let $u\in\mathbb{C}$ be a **candidate** for Diaz's modulus conjecture: $u\neq 0$, $|u|$ algebraic over $\mathbb{Q}$, and $e^{u}$ algebraic over $\mathbb{Q}$.
--
--   Then for every non-zero algebraic number $a\in\overline{\mathbb{Q}}^{\times}$, the distance $|u-a|$ is transcendental over $\mathbb{Q}$. Equivalently: a candidate lies on no circle of algebraic radius about a non-zero algebraic centre.
--
--   $$\forall\, a\in\overline{\mathbb{Q}}^{\times},\quad |u-a|\notin\overline{\mathbb{Q}}.$$
--
--   If $|u-a|$ were algebraic then so would be $2\operatorname{Re}(\bar a\, u)=|u|^{2}+|a|^{2}-|u-a|^{2}$, which is an affine relation $Ax+By=C$ with real algebraic coefficients and $(A,B)\neq(0,0)$. That contradicts the cheap line exclusion for candidates. The exclusion of $a=0$ is essential: $|u|$ is algebraic by hypothesis.
-- source:
--   Carlo Perassi, companion note to https://github.com/carlok/diaz-modulus-lean, version 1.9, 25 September 2026 (GitHub release note-v1.9), Corollary 6.3. Background: G. Diaz, J. Théor. Nombres Bordeaux 16 (2004), 535–553, §5.1.

import Mathlib
import Definitions.Def_DiazModulus

open Complex ComplexConjugate

namespace DiazModulus
theorem candidate_distance_transcendental {u : ℂ} (h : IsCandidate u)
    {a : ℂ} (ha : IsAlgebraic ℚ a) (ha0 : a ≠ 0) :
    Transcendental ℚ ((‖u - a‖ : ℝ) : ℂ) := by sorry
end DiazModulus
