-- Prove2me | Theorems.Thm_BoydADMM_Prox_prox_l1_eq_softThreshold
-- name    : BoydADMM.Prox.prox_l1_eq_softThreshold
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-06T01:54:59.236265+00:00
-- url     : https://prove2.me/theorems/149644f2-e5ad-4c5e-96fc-fa1d6e0c4f1f
-- title:
--   §4.4.3, p. 32 — soft thresholding is the proximity operator of the ℓ1 norm
-- statement:
--   Let $\lambda>0$, $\rho>0$ and $v\in\mathbb R^n$, and take $f(x)=\lambda\|x\|_1$ and $A=I$. Then the $x$-update
--   $$x^+=\mathbf{prox}_{f,\rho}(v)=\operatorname*{argmin}_{x\in\mathbb R^n}\Bigl(\lambda\|x\|_1+\tfrac{\rho}{2}\|x-v\|_2^2\Bigr)$$
--   is unique and is given componentwise by soft thresholding:
--   $$x_i^+=S_{\lambda/\rho}(v_i),\qquad i=1,\dots,n.$$
--   That is, $x\in\mathbb R^n$ minimizes $\lambda\|x\|_1+\tfrac{\rho}{2}\|x-v\|_2^2$ if and only if $x=(S_{\lambda/\rho}(v_1),\dots,S_{\lambda/\rho}(v_n))$. In the language of §4.1, soft thresholding is the proximity operator of the $\ell_1$ norm.
--
--   Elementwise soft thresholding is the update used by every $\ell_1$-regularized problem in the rest of the book: the lasso, basis pursuit, sparse inverse covariance selection and their distributed versions.
--
--   **Formalization Note** $\|x\|_1=\sum_i|x_i|$ is written out as a sum; $\|\cdot\|_2$ is the norm of `EuclideanSpace ℝ (Fin n)`. The book writes "the solution"; the objective is strictly convex, so the statement is an equivalence giving both minimality and uniqueness. The minimization is over all of $\mathbb R^n$ ($\operatorname{dom} f=\mathbb R^n$). $\lambda$ is written `lam`.
-- source:
--   Boyd, Parikh, Chu, Peleato, Eckstein, Distributed Optimization and Statistical Learning via the Alternating Direction Method of Multipliers, Found. Trends Mach. Learn. 3(1) (2011), p. 32, §4.4.3

import Mathlib
import Definitions.Def_BoydADMM_Prox_Basic

open Matrix

namespace BoydADMM.Prox

theorem prox_l1_eq_softThreshold {n : ℕ} (lam ρ : ℝ) (hlam : 0 < lam) (hρ : 0 < ρ)
    (v x : EuclideanSpace ℝ (Fin n)) :
    IsProx Set.univ (fun y => lam * l1Norm y) ρ v x ↔ x = softThresholdVec (lam / ρ) v := by sorry

end BoydADMM.Prox
