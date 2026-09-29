-- Prove2me | Theorems.Thm_ClassicalDynamics_hamiltonian_conserved
-- name    : ClassicalDynamics.hamiltonian_conserved
-- status  : Proved
-- author  : @Lucas
-- created : 2026-09-22T23:39:14.363605+00:00
-- url     : https://prove2.me/theorems/b2932b8a-27e3-49ec-862a-456f1721e624
-- title:
--   $\partial L/\partial t = 0$ implies the Hamiltonian is conserved
-- statement:
--   **Tong, eq. (2.47).** If a smooth Lagrangian $L$ does not depend explicitly on time, i.e. $\partial L/\partial t = 0$ everywhere, then along any smooth solution of Lagrange's equations the Hamiltonian
--   $$H = \sum_j \dot q_j \frac{\partial L}{\partial \dot q_j} - L$$
--   is a constant of the motion: it takes the same value at all times. $H$, written as a function of the coordinates and the conjugate momenta, is usually identified with the total energy of the system.
-- source:
--   D. Tong, Classical Dynamics, University of Cambridge Part II Mathematical Tripos, Michaelmas 2004/2005, https://www.damtp.cam.ac.uk/user/tong/dynamics.html, Section 2 (pp. 10-25), p. 23, eqs. (2.47)-(2.48)

import Definitions.Def_ClassicalDynamics_core

namespace ClassicalDynamics

/-- Tong, eq. (2.47): if `∂L/∂t = 0` then the Hamiltonian is a constant of the motion. -/
theorem hamiltonian_conserved {n : ℕ} (L : Lagrangian n)
    (hL : IsSmoothLagrangian L)
    (hLt : ∀ (t : ℝ) (x v : Fin n → ℝ), deriv (fun s : ℝ => L s x v) t = 0)
    (q : ℝ → Fin n → ℝ) (hq : ContDiff ℝ (⊤ : ℕ∞) q) (hmot : IsMotion L q) :
    IsConstantInTime (fun t => hamiltonian L t (q t) (vel q t)) := by sorry
end ClassicalDynamics
