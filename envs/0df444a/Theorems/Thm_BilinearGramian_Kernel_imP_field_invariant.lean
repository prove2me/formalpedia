-- Prove2me | Theorems.Thm_BilinearGramian_Kernel_imP_field_invariant
-- name    : BilinearGramian.Kernel.imP_field_invariant
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T06:39:19.557733+00:00
-- url     : https://prove2.me/theorems/daecf1b5-4213-449f-a389-0f83dc172062
-- title:
--   Theorem 3.1(a), proof — $\mathrm{Im}\,P$ is invariant under the vector field of (3.1)
-- statement:
--   Let $A, N_1,\dots,N_m \in\mathbb R^{n\times n}$ and $B\in\mathbb R^{n\times m}$, and let $P\in\mathbb R^{n\times n}$ be nonnegative definite and solve
--   $$AP + PA^T + \sum_{j=1}^m N_j P N_j^T = -BB^T.$$
--   Then for every state $z\in\mathrm{Im}\,P$ and every input value $w = (w_1,\dots,w_m)\in\mathbb R^m$,
--   $$Az + \sum_{j=1}^m w_j N_j z + Bw \in \mathrm{Im}\,P .$$
--   In the words of the paper: if $x(t)\in\mathrm{Im}\,P$, then $\dot x(t)\in\mathrm{Im}\,P$, whatever the current input value $u(t)$; $\mathrm{Im}\,P$ is invariant under the dynamics of the bilinear system (3.1).
--
--   This pointwise statement about the vector field is the algebraic content of part (a) of Theorem 3.1; the remaining step passes from the vector field to trajectories.
-- source:
--   Benner, Damm, Lyapunov Equations, Energy Functionals, and Model Order Reduction of Bilinear and Stochastic Systems, SIAM J. Control Optim. 49(2) (2011), p. 696, Theorem 3.1, proof of (a)

import Mathlib
import Definitions.Def_BilinearGramian_Kernel_System
import Definitions.Def_BilinearGramian_Kernel_GramianEquations

open Matrix

namespace BilinearGramian.Kernel

/-- Benner–Damm 2011, Theorem 3.1, proof of (a), p. 696: if `P ≥ 0` solves the first equation of
(3.6), then `Im P` is invariant under the vector field of (3.1): for every state `z ∈ Im P` and
every input value `w ∈ ℝᵐ`, `A z + ∑_j N_j z w_j + B w ∈ Im P`. -/
theorem imP_field_invariant {n m : ℕ} (A : Matrix (Fin n) (Fin n) ℝ)
    (N : Fin m → Matrix (Fin n) (Fin n) ℝ) (B : Matrix (Fin n) (Fin m) ℝ)
    (P : Matrix (Fin n) (Fin n) ℝ) (hP : P.PosSemidef) (hPeq : ReachGramianEq A N B P)
    (z : Fin n → ℝ) (hz : z ∈ LinearMap.range (Matrix.toLin' P)) (w : Fin m → ℝ) :
    field A N B z w ∈ LinearMap.range (Matrix.toLin' P) := by sorry

end BilinearGramian.Kernel
