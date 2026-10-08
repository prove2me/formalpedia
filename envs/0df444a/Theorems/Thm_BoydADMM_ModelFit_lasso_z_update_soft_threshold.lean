-- Prove2me | Theorems.Thm_BoydADMM_ModelFit_lasso_z_update_soft_threshold
-- name    : BoydADMM.ModelFit.lasso_z_update_soft_threshold
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-06T08:36:33.365119+00:00
-- url     : https://prove2.me/theorems/86af2a4e-b8ff-44ad-961f-65c9dd3b3d43
-- title:
--   §8.2.1, p. 65 — the distributed-lasso z-update is z = S_{λ/ρN}(x̄ + ū)
-- statement:
--   Let $N\ge 1$ be the number of data blocks, $\lambda>0$, $\rho>0$, and let $x_1,\dots,x_N,u_1,\dots,u_N\in\mathbb R^n$ be the local variables $x_i^{k+1}$ and scaled dual variables $u_i^k$, with averages $\bar x=\frac1N\sum_i x_i$ and $\bar u=\frac1N\sum_i u_i$. With the lasso regularizer $r(z)=\lambda\|z\|_1$, the $z$-update of global-consensus ADMM minimizes
--   $$\lambda\|z\|_1+\frac{N\rho}{2}\|z-\bar x-\bar u\|_2^2 .$$
--   A point $z\in\mathbb R^n$ minimizes this function if and only if, for every component $j$,
--   $$z_j=S_{\lambda/(\rho N)}\bigl(\bar x_j+\bar u_j\bigr),$$
--   where $S_\kappa$ is the soft thresholding operator. In particular the minimizer is unique.
--
--   This is the gathering step of the distributed lasso: after averaging, the consensus update is a componentwise soft thresholding.
--
--   **Formalization Note** The book writes the threshold as $\lambda/\rho N$, meaning $\lambda/(\rho N)$. The objective is the general $z$-update of p. 65 with $r=\lambda\|\cdot\|_1$ (the lasso regularizer of §8.1.1, p. 62). The statement is an equivalence, which includes existence and uniqueness. $\lambda$ is `lam` in Lean.
-- source:
--   Boyd, Parikh, Chu, Peleato, Eckstein, Distributed Optimization and Statistical Learning via the Alternating Direction Method of Multipliers, Found. Trends Mach. Learn. 3(1) (2011), p. 65, §8.2 (z-update) and §8.2.1

import Mathlib
import Definitions.Def_BoydADMM_ModelFit_Basic

open Matrix

namespace BoydADMM.ModelFit

/-- §8.2.1, p. 65: the distributed-lasso `z`-update
`argmin_z (λ‖z‖₁ + (Nρ/2)‖z − x̄ − ū‖₂²)` is soft thresholding `S_{λ/(ρN)}(x̄ + ū)`, componentwise. -/
theorem lasso_z_update_soft_threshold {N n : ℕ} (hN : 0 < N)
    (x u : Fin N → EuclideanSpace ℝ (Fin n)) (lam ρ : ℝ) (hlam : 0 < lam) (hρ : 0 < ρ)
    (z : EuclideanSpace ℝ (Fin n)) :
    IsMinOn (fun z' : EuclideanSpace ℝ (Fin n) =>
        lam * l1norm z' + (N : ℝ) * ρ / 2 *
          ‖z' - (N : ℝ)⁻¹ • (∑ i, x i) - (N : ℝ)⁻¹ • (∑ i, u i)‖ ^ 2) Set.univ z ↔
      ∀ j, z j = BoydADMM.Prox.softThreshold (lam / (ρ * N))
        (((N : ℝ)⁻¹ • (∑ i, x i)) j + ((N : ℝ)⁻¹ • (∑ i, u i)) j) := by sorry

end BoydADMM.ModelFit
