-- Prove2me | Theorems.Thm_BoydADMM_Prox_quadratic_affine_kkt
-- name    : BoydADMM.Prox.quadratic_affine_kkt
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-06T01:54:36.764233+00:00
-- url     : https://prove2.me/theorems/4c009250-6fa6-4254-a387-066e614a6f85
-- title:
--   §4.2.5, p. 29 — quadratic f restricted to {Fx = g}: the x-update solves the KKT system and is affine in v
-- statement:
--   Let $f(x)=\tfrac12x^TPx+q^Tx+r$ with $P\in\mathbf S^n_+$, restricted to the affine set $\operatorname{dom} f=\{x\mid Fx=g\}$, where $F\in\mathbb R^{m\times n}$ and $g\in\mathbb R^m$ are arbitrary. Let $\rho>0$. Consider the scaled-form $x$-update with $A=I$ and $v=z^k-u^k$:
--   $$x^{k+1}=\operatorname*{argmin}_{Fx=g}\Bigl(f(x)+\tfrac{\rho}{2}\|x-z^k+u^k\|_2^2\Bigr).$$
--
--   1. For all $z^k,u^k\in\mathbb R^n$, a point $x^{k+1}$ is such a minimizer if and only if there is $\nu\in\mathbb R^m$ solving the KKT system
--   $$\begin{bmatrix}P+\rho I & F^T\\ F & 0\end{bmatrix}\begin{bmatrix}x^{k+1}\\ \nu\end{bmatrix}+\begin{bmatrix}q-\rho(z^k-u^k)\\ -g\end{bmatrix}=0.$$
--   2. If the affine set $\{x\mid Fx=g\}$ is nonempty, then $x^+$ is an affine function of $v$: there are a matrix $M\in\mathbb R^{n\times n}$ and a vector $b\in\mathbb R^n$ such that for every $v$, the minimizer of $f(x)+\tfrac{\rho}{2}\|x-v\|_2^2$ over $\{Fx=g\}$ is unique and equals $Mv+b$.
--
--   So the update with an equality-constrained quadratic term again reduces to one linear system, the KKT system, whose coefficient matrix does not depend on $v$.
--
--   **Formalization Note** The book says "the update involves solving the KKT system"; we state the equivalence between minimality and solvability of the KKT system for some multiplier $\nu$ (sufficiency is the direction the book uses; necessity holds because the constraints are linear). $F$ may have any rank, so $\nu$ need not be unique. Existence of a minimizer needs the affine set to be nonempty, which the book leaves implicit; it is a hypothesis of part 2 only.
-- source:
--   Boyd, Parikh, Chu, Peleato, Eckstein, Distributed Optimization and Statistical Learning via the Alternating Direction Method of Multipliers, Found. Trends Mach. Learn. 3(1) (2011), p. 29, §4.2.5

import Mathlib
import Definitions.Def_BoydADMM_Prox_Basic

open Matrix

namespace BoydADMM.Prox

theorem quadratic_affine_kkt {n m : ℕ} (P : Matrix (Fin n) (Fin n) ℝ) (hP : P.PosSemidef)
    (q : EuclideanSpace ℝ (Fin n)) (r : ℝ) (F : Matrix (Fin m) (Fin n) ℝ)
    (g : EuclideanSpace ℝ (Fin m)) (ρ : ℝ) (hρ : 0 < ρ) :
    (∀ (z u x : EuclideanSpace ℝ (Fin n)),
        IsProx (affineSet F g) (quadObj P q r) ρ (z - u) x ↔
          ∃ ν : EuclideanSpace ℝ (Fin m),
            Matrix.toEuclideanLin (P + ρ • (1 : Matrix (Fin n) (Fin n) ℝ)) x
                + Matrix.toEuclideanLin Fᵀ ν + (q - ρ • (z - u)) = 0 ∧
              Matrix.toEuclideanLin F x - g = 0) ∧
      ((affineSet F g).Nonempty →
        ∃ (M : Matrix (Fin n) (Fin n) ℝ) (b : EuclideanSpace ℝ (Fin n)),
          ∀ (v x : EuclideanSpace ℝ (Fin n)),
            IsProx (affineSet F g) (quadObj P q r) ρ v x ↔
              x = Matrix.toEuclideanLin M v + b) := by sorry

end BoydADMM.Prox
