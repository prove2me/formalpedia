-- Prove2me | Theorems.Thm_BoydADMM_L1_huber_z_update
-- name    : BoydADMM.L1.huber_z_update
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-06T08:05:27.571324+00:00
-- url     : https://prove2.me/theorems/b07dc7fc-2942-4b6b-9676-57dfc5dc58da
-- title:
--   §6.1.1, p. 40 — the Huber-fitting z-update is $\frac{\rho}{1+\rho}v+\frac{1}{1+\rho}S_{1+1/\rho}(v)$, $v=Ax^{k+1}-b+u^k$
-- statement:
--   Let $A\in\mathbb R^{m\times n}$, $b,u\in\mathbb R^m$, $x\in\mathbb R^n$ and $\rho>0$, and put $v=Ax-b+u$. The vector $z^\star\in\mathbb R^m$ with components
--   $$z^\star_i=\frac{\rho}{1+\rho}\,v_i+\frac{1}{1+\rho}\,S_{1+1/\rho}(v_i)$$
--   is the unique minimizer over $z\in\mathbb R^m$ of
--   $$g^{\mathrm{hub}}(z)+\frac\rho2\|Ax-z-b+u\|_2^2,$$
--   where $g^{\mathrm{hub}}(z)=\sum_i g^{\mathrm{hub}}(z_i)$ is the Huber penalty with transition at level $1$ and $S_\kappa$ is soft thresholding applied elementwise.
--
--   With $x=x^{k+1}$ and $u=u^k$ this is the z-update of scaled-form ADMM for Huber fitting, minimize $g^{\mathrm{hub}}(Ax-b)$, written with the constraint $Ax-z=b$: the proximity operator of the Huber function.
--
--   **Formalization Note** Vectors are `EuclideanSpace ℝ (Fin m)` and $A$ acts by `Matrix.toEuclideanLin`. The formula is applied componentwise, as the book's $S_{1+1/\rho}$ is.
-- source:
--   Boyd, Parikh, Chu, Peleato, Eckstein, Distributed Optimization and Statistical Learning via the Alternating Direction Method of Multipliers, Found. Trends Mach. Learn. 3(1) (2011), p. 40, §6.1.1 (Huber fitting); ADMM form from §6.1, p. 39

import Mathlib
import Definitions.Def_BoydADMM_L1_Basic

open Matrix

namespace BoydADMM.L1

/-- §6.1.1, p. 40: for `ρ > 0`, with `v = Ax − b + u`, the vector with components
`(ρ/(1+ρ)) v_i + (1/(1+ρ)) S_{1+1/ρ}(v_i)` is the unique minimizer of
`g^hub(z) + (ρ/2)‖Ax − z − b + u‖₂²` over `z ∈ ℝᵐ`. -/
theorem huber_z_update {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (b u : EuclideanSpace ℝ (Fin m))
    (x : EuclideanSpace ℝ (Fin n)) (ρ : ℝ) (hρ : 0 < ρ) :
    IsUniqueMinimizerOn
      (fun z : EuclideanSpace ℝ (Fin m) =>
        huberVec z + (ρ / 2) * ‖Matrix.toEuclideanLin A x - z - b + u‖ ^ 2) Set.univ
      (WithLp.toLp 2 fun i =>
        ρ / (1 + ρ) * (Matrix.toEuclideanLin A x - b + u) i +
          1 / (1 + ρ) * BoydADMM.Prox.softThreshold (1 + 1 / ρ) ((Matrix.toEuclideanLin A x - b + u) i)) := by sorry

end BoydADMM.L1
