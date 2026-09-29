-- Prove2me | Theorems.Thm_ClassicalDynamics_ignorable_coordinate_momentum_conserved
-- name    : ClassicalDynamics.ignorable_coordinate_momentum_conserved
-- status  : Proved
-- author  : @Lucas
-- created : 2026-09-22T23:40:28.759705+00:00
-- url     : https://prove2.me/theorems/97f48d9b-5bca-4f8a-9c46-3aded4c4559f
-- title:
--   An ignorable (cyclic) coordinate has conserved conjugate momentum
-- statement:
--   **Tong, eq. (2.49).** Suppose a smooth Lagrangian $L$ on $\mathbb{R}^n$ satisfies $\partial L/\partial q_j = 0$ identically for some coordinate $q_j$; such a coordinate is called *ignorable* or *cyclic*. Then along any smooth solution of Lagrange's equations the conjugate momentum
--   $$p_j = \frac{\partial L}{\partial \dot q_j}$$
--   is a constant of the motion, since Lagrange's equation for that coordinate reads $\dot p_j = \partial L/\partial q_j = 0$.
-- source:
--   D. Tong, Classical Dynamics, University of Cambridge Part II Mathematical Tripos, Michaelmas 2004/2005, https://www.damtp.cam.ac.uk/user/tong/dynamics.html, Section 2 (pp. 10-25), p. 23, eqs. (2.49)-(2.50)

import Definitions.Def_ClassicalDynamics_core

namespace ClassicalDynamics

/-- Tong, eq. (2.49): the momentum conjugate to an ignorable (cyclic) coordinate
is a constant of the motion. -/
theorem ignorable_coordinate_momentum_conserved {n : ℕ} (L : Lagrangian n)
    (hL : IsSmoothLagrangian L) (j : Fin n)
    (hcyc : ∀ (t : ℝ) (x v : Fin n → ℝ), dLdq L j t x v = 0)
    (q : ℝ → Fin n → ℝ) (hq : ContDiff ℝ (⊤ : ℕ∞) q) (hmot : IsMotion L q) :
    IsConstantInTime (momentum L j q) := by sorry
end ClassicalDynamics
