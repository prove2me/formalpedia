-- Prove2me | Theorems.Thm_DetComplexityPowerSum_Quadratic_claim_3_6
-- name    : DetComplexityPowerSum.Quadratic.claim_3_6
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T08:31:55.084403+00:00
-- url     : https://prove2.me/theorems/816c9f5e-83a6-4ee4-af27-0e05028008de
-- title:
--   Claim 3.6 — vectors $g,h$ non-vanishing on all kernel vectors over $S$
-- statement:
--   Let $n\ge 2$ and $\det M(x)=\sum_{i=1}^nx_i^n$ as polynomials. Let
--   $$U=\bigcup_{a\in S}\{u:u\ne0,\ u^TM(a)=0\},\qquad V=\bigcup_{a\in S}\{v:v\ne0,\ M(a)v=0\}.$$
--   Then there exist vectors $g,h\in\mathbb C^m$ such that $g^Tu\ne0$ and $h^Tv\ne0$ for every $u\in U$ and $v\in V$.
--
--   The two vectors work simultaneously for every non-zero kernel vector at every point of $S$. They are what makes the lift of a point of $S$ to the proxy system unique.
--
--   Differences from the source:
--   - encoding: 1-based coordinates $x_{n-1}$ and $i\le n-2$ → 0-based `Fin n` with `IsPenultimate` (`i + 2 = n`) and `IsEarly` (`i + 2 < n`); reason: the same coordinates under the shift by one
-- source:
--   Mrinal Kumar, Ben Lee Volk, STOC 2027 submission #131 (October 2026), p. 7, Claim 3.6

import Mathlib
import Definitions.Def_PermanentCubic
import Definitions.Def_DetComplexityPowerSum_Quadratic_KernelNormalizers
open OAI.PermanentBorder

namespace DetComplexityPowerSum.Quadratic

theorem claim_3_6 {n m : ℕ} (M₀ : Matrix (Fin m) (Fin m) ℂ)
    (M : Fin n → Matrix (Fin m) (Fin m) ℂ) (hn : 2 ≤ n)
    (hrep : affineMatrixPolynomial m M₀ M = powerSum n) :
    ∃ g h : Fin m → ℂ, NormalizesKernels M₀ M g h := by sorry

end DetComplexityPowerSum.Quadratic
