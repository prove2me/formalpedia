-- Prove2me | Theorems.Thm_BilinearGramian_Kernel_kerP_subset
-- name    : BilinearGramian.Kernel.kerP_subset
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T06:39:26.333367+00:00
-- url     : https://prove2.me/theorems/ee36d92f-f639-45f2-afb8-d8bd980299e2
-- title:
--   Theorem 3.1(a), proof — $N_j^T\,\mathrm{Ker}\,P \subset \mathrm{Ker}\,P \subset \mathrm{Ker}\,B^T$
-- statement:
--   Let $A, N_1,\dots,N_m \in\mathbb R^{n\times n}$ and $B\in\mathbb R^{n\times m}$, and let $P\in\mathbb R^{n\times n}$ be nonnegative definite and solve the first generalized Lyapunov equation of (3.6),
--   $$AP + PA^T + \sum_{j=1}^m N_j P N_j^T = -BB^T.$$
--   Then
--   $$N_j^T\,\mathrm{Ker}\,P \subset \mathrm{Ker}\,P \quad (j=1,\dots,m), \qquad \mathrm{Ker}\,P \subset \mathrm{Ker}\,B^T .$$
--   Equivalently: if $Pv = 0$, then $B^Tv = 0$ and $PN_j^Tv = 0$ for every $j$.
--
--   This is the first step of the proof that states reachable from $0$ lie in the image of the controllability Gramian.
-- source:
--   Benner, Damm, Lyapunov Equations, Energy Functionals, and Model Order Reduction of Bilinear and Stochastic Systems, SIAM J. Control Optim. 49(2) (2011), p. 695, Theorem 3.1, proof of (a)

import Mathlib
import Definitions.Def_BilinearGramian_Kernel_GramianEquations

open Matrix

namespace BilinearGramian.Kernel

/-- Benner–Damm 2011, Theorem 3.1, proof of (a), p. 695: if `P ≥ 0` solves the first equation of
(3.6), then `N_jᵀ Ker P ⊂ Ker P ⊂ Ker Bᵀ` for every `j`. -/
theorem kerP_subset {n m : ℕ} (A : Matrix (Fin n) (Fin n) ℝ)
    (N : Fin m → Matrix (Fin n) (Fin n) ℝ) (B : Matrix (Fin n) (Fin m) ℝ)
    (P : Matrix (Fin n) (Fin n) ℝ) (hP : P.PosSemidef) (hPeq : ReachGramianEq A N B P) :
    (∀ j : Fin m,
      (LinearMap.ker (Matrix.toLin' P)).map (Matrix.toLin' (N j)ᵀ) ≤
        LinearMap.ker (Matrix.toLin' P)) ∧
    LinearMap.ker (Matrix.toLin' P) ≤ LinearMap.ker (Matrix.toLin' Bᵀ) := by sorry

end BilinearGramian.Kernel
