-- Prove2me | Theorems.Thm_FenchelRobust_Counterpart_support_uncertaintySet
-- name    : FenchelRobust.Counterpart.support_uncertaintySet
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-05T09:29:59.488744+00:00
-- url     : https://prove2.me/theorems/30d64360-762b-4219-873e-14bafa69ee58
-- title:
--   Eqs. (16)–(18) — support of the affine uncertainty set
-- statement:
--   For $U=\{a^0+A\zeta:\zeta\in Z\}$ and every $v\in\mathbb R^m$,
--   $$\delta^*(v\mid U)=(a^0)^Tv+\delta^*(A^Tv\mid Z).$$
--   This identity transfers support-function calculations from the uncertain vector $a$ to the primitive uncertainty $\zeta$.
--
--   **Formalization Note.** No nonemptiness or convexity is required. Both sides are $-\infty$ when $Z$ is empty. The nominal vector is denoted $a^0$ throughout; equation (16) prints $a_0$ once.
-- source:
--   Ben-Tal, den Hertog, Vial, Deriving robust counterparts of nonlinear uncertain inequalities, CentER Discussion Paper 2012-053 (July 2, 2012), p. 5, Eqs. (16)–(18), proof of Theorem 2

import Mathlib
import Definitions.Def_FenchelRobust_Counterpart_Model

namespace FenchelRobust.Counterpart

/-- Equations (16)–(18): support of the affine image, including the empty set. -/
theorem support_uncertaintySet {m L : ℕ} (a0 : Fin m → ℝ)
    (A : Matrix (Fin m) (Fin L) ℝ) (Z : Set (Fin L → ℝ))
    (v : Fin m → ℝ) :
    supportFun (uncertaintySet a0 A Z) v =
      ((a0 ⬝ᵥ v : ℝ) : EReal) + supportFun Z (Matrix.mulVec A.transpose v) := by sorry

end FenchelRobust.Counterpart
