-- Prove2me | Theorems.Thm_BilinearGramian_Kernel_kerQ_subset
-- name    : BilinearGramian.Kernel.kerQ_subset
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T06:39:30.011977+00:00
-- url     : https://prove2.me/theorems/e7993d7a-d3a2-4985-9555-115d7c5730e7
-- title:
--   Theorem 3.1(b), proof — $N_j\,\mathrm{Ker}\,Q \subset \mathrm{Ker}\,Q \subset \mathrm{Ker}\,C$ and $A\,\mathrm{Ker}\,Q \subset \mathrm{Ker}\,Q$
-- statement:
--   Let $A, N_1,\dots,N_m \in\mathbb R^{n\times n}$ and $C\in\mathbb R^{p\times n}$, and let $Q\in\mathbb R^{n\times n}$ be nonnegative definite and solve the second generalized Lyapunov equation of (3.6),
--   $$A^TQ + QA + \sum_{j=1}^m N_j^T Q N_j = -C^TC.$$
--   Then
--   $$N_j\,\mathrm{Ker}\,Q \subset \mathrm{Ker}\,Q \quad (j = 1,\dots,m), \qquad \mathrm{Ker}\,Q\subset \mathrm{Ker}\,C, \qquad A\,\mathrm{Ker}\,Q \subset \mathrm{Ker}\,Q .$$
--
--   This is the dual of the kernel inclusions for the controllability Gramian, and the first step of the proof that states in $\mathrm{Ker}\,Q$ produce no output.
-- source:
--   Benner, Damm, Lyapunov Equations, Energy Functionals, and Model Order Reduction of Bilinear and Stochastic Systems, SIAM J. Control Optim. 49(2) (2011), p. 696, Theorem 3.1, proof of (b)

import Mathlib
import Definitions.Def_BilinearGramian_Kernel_GramianEquations

open Matrix

namespace BilinearGramian.Kernel

/-- Benner–Damm 2011, Theorem 3.1, proof of (b), p. 696: if `Q ≥ 0` solves the second equation of
(3.6), then `N_j Ker Q ⊂ Ker Q ⊂ Ker C` for every `j`, and `A Ker Q ⊂ Ker Q`. -/
theorem kerQ_subset {n m p : ℕ} (A : Matrix (Fin n) (Fin n) ℝ)
    (N : Fin m → Matrix (Fin n) (Fin n) ℝ) (C : Matrix (Fin p) (Fin n) ℝ)
    (Q : Matrix (Fin n) (Fin n) ℝ) (hQ : Q.PosSemidef) (hQeq : ObsGramianEq A N C Q) :
    (∀ j : Fin m,
      (LinearMap.ker (Matrix.toLin' Q)).map (Matrix.toLin' (N j)) ≤
        LinearMap.ker (Matrix.toLin' Q)) ∧
    LinearMap.ker (Matrix.toLin' Q) ≤ LinearMap.ker (Matrix.toLin' C) ∧
    (LinearMap.ker (Matrix.toLin' Q)).map (Matrix.toLin' A) ≤
      LinearMap.ker (Matrix.toLin' Q) := by sorry

end BilinearGramian.Kernel
