-- Prove2me | Theorems.Thm_BoydADMM_Prox_component_separable
-- name    : BoydADMM.Prox.component_separable
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-06T01:54:46.927865+00:00
-- url     : https://prove2.me/theorems/3fb260c5-30db-4dd7-8cff-a2414cde9f05
-- title:
--   §4.4.2, p. 31 — component separability: the x-update splits into n scalar minimizations
-- statement:
--   Let $f(x)=f_1(x_1)+\cdots+f_n(x_n)$ with $f_i:\mathbb R\to\mathbb R$, let $A\in\mathbb R^{p\times n}$ with $A^TA=\operatorname{diag}(d_1,\dots,d_n)$ diagonal, let $\rho>0$ and $v\in\mathbb R^p$. Then $x\in\mathbb R^n$ is an $x$-update,
--   $$x\in\operatorname*{argmin}_{y\in\mathbb R^n}\Bigl(\sum_{i=1}^n f_i(y_i)+\tfrac{\rho}{2}\|Ay-v\|_2^2\Bigr),$$
--   if and only if, for every $i$, the scalar $x_i$ minimizes
--   $$t\;\mapsto\; f_i(t)+\tfrac{\rho}{2}\bigl(d_i\,t^2-2\,(A^Tv)_i\,t\bigr)$$
--   over $t\in\mathbb R$. For $A=I$ this is the scalar problem $\min_t f_i(t)+\tfrac{\rho}{2}(t-v_i)^2$ (up to the constant $\tfrac{\rho}{2}v_i^2$).
--
--   This is what the book calls component separability: the $x$-minimization is carried out by $n$ independent scalar minimizations. Soft thresholding (§4.4.3) is the case $f_i=\lambda|\cdot|$.
--
--   **Formalization Note** The book does not write the scalar problems out; we write them explicitly, dropping the constant $\tfrac{\rho}{2}\|v\|_2^2$, which does not affect minimizers. The $f_i$ are real-valued, as on the page.
-- source:
--   Boyd, Parikh, Chu, Peleato, Eckstein, Distributed Optimization and Statistical Learning via the Alternating Direction Method of Multipliers, Found. Trends Mach. Learn. 3(1) (2011), p. 31, §4.4.2

import Mathlib
import Definitions.Def_BoydADMM_Prox_Basic

open Matrix

namespace BoydADMM.Prox

theorem component_separable {n p : ℕ} (f : Fin n → ℝ → ℝ) (A : Matrix (Fin p) (Fin n) ℝ)
    (d : Fin n → ℝ) (hdiag : Aᵀ * A = Matrix.diagonal d) (ρ : ℝ) (hρ : 0 < ρ)
    (v : EuclideanSpace ℝ (Fin p)) (x : EuclideanSpace ℝ (Fin n)) :
    IsXUpdate Set.univ (fun y => ∑ i, f i (y i)) ρ A v x ↔
      ∀ i, ∀ t : ℝ,
        f i (x i) + (ρ / 2) * (d i * x i ^ 2 - 2 * (Matrix.toEuclideanLin Aᵀ v) i * x i) ≤
          f i t + (ρ / 2) * (d i * t ^ 2 - 2 * (Matrix.toEuclideanLin Aᵀ v) i * t) := by sorry

end BoydADMM.Prox
