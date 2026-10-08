-- Prove2me | Theorems.Thm_BilinearGramian_Kernel_kerQ_homField_invariant
-- name    : BilinearGramian.Kernel.kerQ_homField_invariant
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T06:39:47.40087+00:00
-- url     : https://prove2.me/theorems/13dbf03e-dc21-42f5-a17e-48d04986ab73
-- title:
--   Theorem 3.1(b), proof — $\mathrm{Ker}\,Q$ is invariant under the vector field of (3.5)
-- statement:
--   Let $A, N_1,\dots,N_m \in\mathbb R^{n\times n}$ and $C\in\mathbb R^{p\times n}$, and let $Q\in\mathbb R^{n\times n}$ be nonnegative definite and solve
--   $$A^TQ + QA + \sum_{j=1}^m N_j^T Q N_j = -C^TC.$$
--   Then for every state $z\in\mathrm{Ker}\,Q$ and every input value $w\in\mathbb R^m$,
--   $$Az + \sum_{j=1}^m w_j N_j z \in \mathrm{Ker}\,Q .$$
--   In the words of the paper: $x(t)\in\mathrm{Ker}\,Q$ implies $\dot x(t)\in\mathrm{Ker}\,Q$ for the homogeneous system (3.5), so $\mathrm{Ker}\,Q$ is invariant under the dynamics.
--
--   This is the algebraic content of part (b) of Theorem 3.1; the remaining step passes from the vector field to trajectories.
-- source:
--   Benner, Damm, Lyapunov Equations, Energy Functionals, and Model Order Reduction of Bilinear and Stochastic Systems, SIAM J. Control Optim. 49(2) (2011), p. 696, Theorem 3.1, proof of (b)

import Mathlib
import Definitions.Def_BilinearGramian_Kernel_System
import Definitions.Def_BilinearGramian_Kernel_GramianEquations

open Matrix

namespace BilinearGramian.Kernel

/-- Benner–Damm 2011, Theorem 3.1, proof of (b), p. 696: if `Q ≥ 0` solves the second equation
of (3.6), then `Ker Q` is invariant under the vector field of the homogeneous system (3.5): for
every state `z ∈ Ker Q` and every input value `w ∈ ℝᵐ`, `A z + ∑_j N_j z w_j ∈ Ker Q`. -/
theorem kerQ_homField_invariant {n m p : ℕ} (A : Matrix (Fin n) (Fin n) ℝ)
    (N : Fin m → Matrix (Fin n) (Fin n) ℝ) (C : Matrix (Fin p) (Fin n) ℝ)
    (Q : Matrix (Fin n) (Fin n) ℝ) (hQ : Q.PosSemidef) (hQeq : ObsGramianEq A N C Q)
    (z : Fin n → ℝ) (hz : z ∈ LinearMap.ker (Matrix.toLin' Q)) (w : Fin m → ℝ) :
    homField A N z w ∈ LinearMap.ker (Matrix.toLin' Q) := by sorry

end BilinearGramian.Kernel
