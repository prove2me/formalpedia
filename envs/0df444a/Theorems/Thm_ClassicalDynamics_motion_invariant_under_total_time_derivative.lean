-- Prove2me | Theorems.Thm_ClassicalDynamics_motion_invariant_under_total_time_derivative
-- name    : ClassicalDynamics.motion_invariant_under_total_time_derivative
-- status  : Proved
-- author  : @Lucas
-- created : 2026-09-22T23:37:58.774188+00:00
-- url     : https://prove2.me/theorems/cc2c83ff-a559-4ffd-b5f9-56772585f00e
-- title:
--   $L$ and $L + df/dt$ have the same equations of motion
-- statement:
--   **Tong, eq. (2.45).** The Lagrangian of a system is not unique: adding to it the total time derivative of any function $f(t, q)$ of time and position leaves the equations of motion unchanged.
--
--   Precisely, let $L$ be a smooth Lagrangian on $\mathbb{R}^n$, let $f(t, q)$ be smooth, and set
--   $$L'(t, q, v) = L(t, q, v) + \frac{df}{dt}, \qquad
--   \frac{df}{dt} = \frac{\partial f}{\partial t} + \sum_{i} v_i \frac{\partial f}{\partial q_i},$$
--   the chain-rule expression for the total time derivative of $f$ along a path with velocity $v$. Then a smooth path satisfies Lagrange's equations for $L$ if and only if it satisfies them for $L'$.
-- source:
--   D. Tong, Classical Dynamics, University of Cambridge Part II Mathematical Tripos, Michaelmas 2004/2005, https://www.damtp.cam.ac.uk/user/tong/dynamics.html, Section 2 (pp. 10-25), p. 22, eq. (2.45)

import Definitions.Def_ClassicalDynamics_core

namespace ClassicalDynamics

/-- Tong, eq. (2.45): adding a total time derivative `df/dt` to a Lagrangian
leaves the equations of motion unchanged. -/
theorem motion_invariant_under_total_time_derivative {n : ℕ} (L : Lagrangian n)
    (hL : IsSmoothLagrangian L) (f : ℝ → (Fin n → ℝ) → ℝ)
    (hf : ContDiff ℝ (⊤ : ℕ∞) (fun p : ℝ × (Fin n → ℝ) => f p.1 p.2))
    (q : ℝ → Fin n → ℝ) (hq : ContDiff ℝ (⊤ : ℕ∞) q) :
    IsMotion L q ↔
      IsMotion (fun t x v =>
        L t x v + (deriv (fun s : ℝ => f s x) t + ∑ i : Fin n, v i * dfdq f i t x)) q := by sorry
end ClassicalDynamics
