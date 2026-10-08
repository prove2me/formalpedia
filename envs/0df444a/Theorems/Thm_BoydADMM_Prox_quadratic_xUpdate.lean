-- Prove2me | Theorems.Thm_BoydADMM_Prox_quadratic_xUpdate
-- name    : BoydADMM.Prox.quadratic_xUpdate
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-06T01:54:30.455184+00:00
-- url     : https://prove2.me/theorems/42357a34-a87a-4faf-871d-013e9bacd962
-- title:
--   (4.1), p. 26 — for quadratic f, x⁺ = (P + ρAᵀA)⁻¹(ρAᵀv − q)
-- statement:
--   Let $f(x)=\tfrac12x^TPx+q^Tx+r$ with $P\in\mathbf S^n_+$ (symmetric positive semidefinite), $q\in\mathbb R^n$, $r\in\mathbb R$. Let $A\in\mathbb R^{p\times n}$, $\rho>0$, and assume that $P+\rho A^TA$ is invertible. Then:
--
--   1. the coefficient matrix $P+\rho A^TA$ is positive definite;
--   2. for every $v\in\mathbb R^p$, the $x$-update $x^+=\operatorname*{argmin}_x\bigl(f(x)+\tfrac{\rho}{2}\|Ax-v\|_2^2\bigr)$ over all of $\mathbb R^n$ is unique and is the affine function of $v$
--   $$x^+=(P+\rho A^TA)^{-1}(\rho A^Tv-q).\tag{4.1}$$
--
--   So computing an $x$-update with a quadratic objective term amounts to solving one linear system with a positive definite coefficient matrix, which is what makes factorization caching (§4.2.3) and the matrix inversion lemma (§4.2.4) useful.
--
--   **Formalization Note** $P\in\mathbf S^n_+$ is `P.PosSemidef` (which includes symmetry). "Assuming $P+\rho A^TA$ is invertible" is the explicit hypothesis `IsUnit (P + ρ • (Aᵀ * A))`. The claim "$x^+$ is given by (4.1)" is stated as an equivalence: $x$ is a minimizer if and only if $x$ equals the right-hand side of (4.1), which gives both existence and uniqueness. The positive definiteness, stated by the book in the next sentence, is the first conjunct.
-- source:
--   Boyd, Parikh, Chu, Peleato, Eckstein, Distributed Optimization and Statistical Learning via the Alternating Direction Method of Multipliers, Found. Trends Mach. Learn. 3(1) (2011), p. 26, §4.2, (4.1)

import Mathlib
import Definitions.Def_BoydADMM_Prox_Basic

open Matrix

namespace BoydADMM.Prox

theorem quadratic_xUpdate {n p : ℕ} (P : Matrix (Fin n) (Fin n) ℝ) (hP : P.PosSemidef)
    (q : EuclideanSpace ℝ (Fin n)) (r : ℝ) (A : Matrix (Fin p) (Fin n) ℝ) (ρ : ℝ) (hρ : 0 < ρ)
    (hinv : IsUnit (P + ρ • (Aᵀ * A))) :
    (P + ρ • (Aᵀ * A)).PosDef ∧
      ∀ (v : EuclideanSpace ℝ (Fin p)) (x : EuclideanSpace ℝ (Fin n)),
        IsXUpdate Set.univ (quadObj P q r) ρ A v x ↔
          x = Matrix.toEuclideanLin (P + ρ • (Aᵀ * A))⁻¹
            (ρ • Matrix.toEuclideanLin Aᵀ v - q) := by sorry

end BoydADMM.Prox
