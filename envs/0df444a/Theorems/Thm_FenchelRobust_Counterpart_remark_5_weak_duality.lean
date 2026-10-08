-- Prove2me | Theorems.Thm_FenchelRobust_Counterpart_remark_5_weak_duality
-- name    : FenchelRobust.Counterpart.remark_5_weak_duality
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-05T09:29:23.544893+00:00
-- url     : https://prove2.me/theorems/457697d3-0781-420f-bcc6-3ae13bd8bda5
-- title:
--   Remark 5 — weak duality for a nonconcave uncertain constraint
-- statement:
--   Let $U=a^0+AZ$ and let $D(x)$ be the effective domain of an arbitrary real function $f(\cdot,x)$. For every decision $x$ and vector $v$,
--   $$\sup_{a\in U\cap D(x)}f(a,x)\le (a^0)^Tv+\delta^*(A^Tv\mid Z)-f_*(v,x).$$
--   Consequently, if the right-hand side is at most zero, then $f(a,x)\le0$ for every $a\in U\cap D(x)$. This is the sufficient direction of the counterpart even when $f$ is not concave in its uncertain argument.
--
--   **Formalization Note.** The paper writes a maximum; the statement uses an extended-real supremum and permits empty or unbounded sets. No concavity, compactness, or regularity assumption is needed for weak duality.
-- source:
--   Ben-Tal, den Hertog, Vial, Deriving robust counterparts of nonlinear uncertain inequalities, CentER Discussion Paper 2012-053 (July 2, 2012), p. 6, Remark 5 following Corollary 3

import Mathlib
import Definitions.Def_FenchelRobust_Counterpart_Model

namespace FenchelRobust.Counterpart

/-- Remark 5 after Corollary 3: the FRC bound holds even without concavity. -/
theorem remark_5_weak_duality {m n L : ℕ} (a0 : Fin m → ℝ)
    (A : Matrix (Fin m) (Fin L) ℝ) (Z : Set (Fin L → ℝ))
    (D : (Fin n → ℝ) → Set (Fin m → ℝ))
    (f : (Fin m → ℝ) → (Fin n → ℝ) → ℝ)
    (x : Fin n → ℝ) (v : Fin m → ℝ) :
    worstCase a0 A Z D f x ≤ frcValue a0 A Z D f x v ∧
      (frcValue a0 A Z D f x v ≤ 0 → RobustFeasible a0 A Z D f x) := by sorry

end FenchelRobust.Counterpart
