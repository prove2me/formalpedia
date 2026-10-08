-- Prove2me | Theorems.Thm_BilinearGramian_Kernel_kerP_At_invariant
-- name    : BilinearGramian.Kernel.kerP_At_invariant
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T06:39:25.01501+00:00
-- url     : https://prove2.me/theorems/b8c202c8-db7a-41bf-86db-e40f2c738674
-- title:
--   Theorem 3.1(a), proof — $A^T\,\mathrm{Ker}\,P \subset \mathrm{Ker}\,P$
-- statement:
--   Let $A, N_1,\dots,N_m \in\mathbb R^{n\times n}$ and $B\in\mathbb R^{n\times m}$, and let $P\in\mathbb R^{n\times n}$ be nonnegative definite and solve
--   $$AP + PA^T + \sum_{j=1}^m N_j P N_j^T = -BB^T.$$
--   Then $\mathrm{Ker}\,P$ is invariant under $A^T$:
--   $$A^T\,\mathrm{Ker}\,P \subset \mathrm{Ker}\,P,$$
--   that is, $Pv = 0$ implies $PA^Tv = 0$.
--
--   Together with the inclusions $N_j^T\,\mathrm{Ker}\,P\subset\mathrm{Ker}\,P\subset\mathrm{Ker}\,B^T$, this is what makes $\mathrm{Im}\,P = (\mathrm{Ker}\,P)^\perp$ invariant under the dynamics of (3.1).
-- source:
--   Benner, Damm, Lyapunov Equations, Energy Functionals, and Model Order Reduction of Bilinear and Stochastic Systems, SIAM J. Control Optim. 49(2) (2011), p. 695, Theorem 3.1, proof of (a)

import Mathlib
import Definitions.Def_BilinearGramian_Kernel_GramianEquations

open Matrix

namespace BilinearGramian.Kernel

/-- Benner–Damm 2011, Theorem 3.1, proof of (a), p. 695: if `P ≥ 0` solves the first equation of
(3.6), then `Aᵀ Ker P ⊂ Ker P`. -/
theorem kerP_At_invariant {n m : ℕ} (A : Matrix (Fin n) (Fin n) ℝ)
    (N : Fin m → Matrix (Fin n) (Fin n) ℝ) (B : Matrix (Fin n) (Fin m) ℝ)
    (P : Matrix (Fin n) (Fin n) ℝ) (hP : P.PosSemidef) (hPeq : ReachGramianEq A N B P) :
    (LinearMap.ker (Matrix.toLin' P)).map (Matrix.toLin' Aᵀ) ≤
      LinearMap.ker (Matrix.toLin' P) := by sorry

end BilinearGramian.Kernel
