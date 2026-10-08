-- Prove2me | Theorems.Thm_BilinearGramian_Kernel_theorem_3_1
-- name    : BilinearGramian.Kernel.theorem_3_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T06:39:49.307737+00:00
-- url     : https://prove2.me/theorems/1ff606b6-223f-40b4-a7a7-1f716e747a32
-- title:
--   Theorem 3.1 — states reached from $0$ lie in $\mathrm{Im}\,P$; states in $\mathrm{Ker}\,Q$ produce zero output
-- statement:
--   Let $A, N_1,\dots,N_m\in\mathbb R^{n\times n}$, $B\in\mathbb R^{n\times m}$ and $C\in\mathbb R^{p\times n}$, and consider the bilinear control system (3.1)–(3.2)
--   $$\dot x = Ax + \sum_{j=1}^m N_j x\,u_j + Bu,\qquad y = Cx,$$
--   and the homogeneous bilinear system (3.5), $\dot x = Ax + \sum_{j=1}^m N_j x\,u_j$, $y = Cx$. Inputs $u:[0,\infty)\to\mathbb R^m$ are integrable on every compact interval, and solutions are understood in the integral (Carathéodory) sense.
--
--   1. **(Reachability.)** Let $P\in\mathbb R^{n\times n}$ be nonnegative definite and satisfy $AP + PA^T + \sum_{j=1}^m N_jPN_j^T = -BB^T$. Then for every input $u$, every solution $x(t) = x(t,0,u)$ of (3.1) with $x(0) = 0$ satisfies
--   $$x(t, 0, u)\in \mathrm{Im}\,P \qquad\text{for all } t\ge 0 .$$
--   2. **(Observability.)** Let $Q\in\mathbb R^{n\times n}$ be nonnegative definite and satisfy $A^TQ + QA + \sum_{j=1}^m N_j^TQN_j = -C^TC$, and let $x_0\in\mathrm{Ker}\,Q$. Then for every input $u$, every solution $x(t) = x(t,x_0,u)$ of (3.5) with $x(0) = x_0$ has zero output:
--   $$y(t,x_0,u) = Cx(t,x_0,u) = 0 \qquad\text{for all } t\ge 0 .$$
--
--   Part 1 says that states outside the image of the controllability Gramian cannot be reached from the origin (their controllability energy $E_c$ is infinite); part 2 says that states in the kernel of the observability Gramian are indistinguishable from $0$ at the output (their observability energy $E_o$ vanishes). This is the structural justification for balanced truncation of bilinear systems: such states can be removed without changing the input–output behaviour.
--
--   **Formalization Note** No stability of $A$ and no uniqueness of $P$, $Q$ is assumed: any nonnegative definite solution of (3.6) works, as in the paper. Part 2 is stated for every input $u$, not only $u = 0$ as printed in the theorem; the paper's proof establishes this stronger form ("$x(t,x_0,u)\in\mathrm{Ker}\,Q$ for all $t\ge0$, implying $y(t,x_0,u) = 0$"), and it is what the clause "i.e., $E_o(x_0) = 0$" requires. The restatements through the energy functionals $E_c$, $E_o$ of (3.3)–(3.4) are not formalized. Solutions are any continuous functions satisfying the integral equation on $[0,\infty)$, so no uniqueness theorem is presupposed.
-- source:
--   Benner, Damm, Lyapunov Equations, Energy Functionals, and Model Order Reduction of Bilinear and Stochastic Systems, SIAM J. Control Optim. 49(2) (2011), p. 695, Theorem 3.1

import Mathlib
import Definitions.Def_BilinearGramian_Kernel_System
import Definitions.Def_BilinearGramian_Kernel_GramianEquations

open Matrix

namespace BilinearGramian.Kernel

/-- Benner–Damm 2011, Theorem 3.1, p. 695.
(a) If `P ≥ 0` solves the first equation of (3.6), every solution of the bilinear system (3.1)
started at `x(0) = 0` stays in `Im P` for all `t ≥ 0`, for every admissible input `u`.
(b) If `Q ≥ 0` solves the second equation of (3.6) and `x0 ∈ Ker Q`, every solution of the
homogeneous bilinear system (3.5) started at `x0` has output `y(t) = C x(t) = 0` for all `t ≥ 0`,
for every admissible input `u` (in particular for `u = 0`). -/
theorem theorem_3_1 {n m p : ℕ} (A : Matrix (Fin n) (Fin n) ℝ)
    (N : Fin m → Matrix (Fin n) (Fin n) ℝ) (B : Matrix (Fin n) (Fin m) ℝ)
    (C : Matrix (Fin p) (Fin n) ℝ) :
    (∀ P : Matrix (Fin n) (Fin n) ℝ, P.PosSemidef → ReachGramianEq A N B P →
      ∀ (u : ℝ → Fin m → ℝ) (x : ℝ → Fin n → ℝ), IsInput u → IsSolution A N B u 0 x →
        ∀ t : ℝ, 0 ≤ t → x t ∈ LinearMap.range (Matrix.toLin' P)) ∧
    (∀ Q : Matrix (Fin n) (Fin n) ℝ, Q.PosSemidef → ObsGramianEq A N C Q →
      ∀ x0 : Fin n → ℝ, x0 ∈ LinearMap.ker (Matrix.toLin' Q) →
        ∀ (u : ℝ → Fin m → ℝ) (x : ℝ → Fin n → ℝ), IsInput u → IsHomSolution A N u x0 x →
          ∀ t : ℝ, 0 ≤ t → C *ᵥ x t = 0) := by sorry

end BilinearGramian.Kernel
