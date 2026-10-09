-- Prove2me | Theorems.Thm_ExtraConsensus_Sublinear_eq_3_20
-- name    : ExtraConsensus.Sublinear.eq_3_20
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T08:17:54.401229+00:00
-- url     : https://prove2.me/theorems/53dfd398-60e6-4c65-8847-8b7563db536e
-- title:
--   Eq. (3.20), p. 13 — ‖z^k − z^{k+1}‖²_G = ‖x^{k+1}‖²_{W̃−W} + ‖(I − W̃)x^k + Uq^k + α∇f(x^k)‖²_W̃ ≥ …
-- statement:
--   Assume Assumption 1, $U=U^{\mathsf T}\succeq0$ with $U^2=\tilde W-W$, any $\alpha$, and let $\mathbf x^k$ be the EXTRA iterates from any $\mathbf x^0$, $\mathbf q^k=\sum_{t\le k}U\mathbf x^t$, $\mathbf z^k=(\mathbf q^k;\mathbf x^k)$. Then for every $\rho>1$ and every $k\ge0$
--   $$\begin{aligned}\|\mathbf z^k-\mathbf z^{k+1}\|_G^2&=\|\mathbf q^k-\mathbf q^{k+1}\|_F^2+\|\mathbf x^k-\mathbf x^{k+1}\|_{\tilde W}^2\\&=\|\mathbf x^{k+1}\|_{\tilde W-W}^2+\|(I-\tilde W)\mathbf x^k+U\mathbf q^k+\alpha\nabla\mathbf f(\mathbf x^k)\|_{\tilde W}^2\\&\ge\|\mathbf x^{k+1}\|_{\tilde W-W}^2+\frac1\rho\|U\mathbf q^k+\alpha\nabla\mathbf f(\mathbf x^k)\|_{\tilde W}^2-\frac1{\rho-1}\|(I-\tilde W)\mathbf x^k\|_{\tilde W}^2 .\end{aligned}$$
--
--   This bounds the optimality residuals of Theorem 3.5(3)–(4) by the progress $\|\mathbf z^k-\mathbf z^{k+1}\|_G^2$.
--
--   **Formalization Note** The page applies the basic inequality $\|\mathbf a+\mathbf b\|^2\ge\frac1\rho\|\mathbf a\|^2-\frac1{\rho-1}\|\mathbf b\|^2$ in the $\tilde W$-norm, which uses $\tilde W\succeq0$ from Assumption 1.
-- source:
--   Shi, Ling, Wu & Yin, arXiv:1404.6264v4, §3.2, proof of Theorem 3.5, eq. (3.20), p. 13

import Mathlib
import Definitions.Def_ExtraConsensus_Sublinear_Model

namespace ExtraConsensus.Sublinear

open Matrix Filter Topology Asymptotics

/-- Eq. (3.20), p. 13. Under Assumption 1, with `U` the symmetric positive semidefinite square root
of `W̃ − W`, for every `ρ > 1` and every `k`:
`‖𝐳ᵏ − 𝐳^{k+1}‖²_G = ‖𝐪ᵏ − 𝐪^{k+1}‖²_F + ‖𝐱ᵏ − 𝐱^{k+1}‖²_{W̃}
  = ‖𝐱^{k+1}‖²_{W̃−W} + ‖(I − W̃)𝐱ᵏ + U𝐪ᵏ + α∇𝐟(𝐱ᵏ)‖²_{W̃}
  ≥ ‖𝐱^{k+1}‖²_{W̃−W} + (1/ρ)‖U𝐪ᵏ + α∇𝐟(𝐱ᵏ)‖²_{W̃} − (1/(ρ−1))‖(I − W̃)𝐱ᵏ‖²_{W̃}`. -/
theorem eq_3_20 {n p : ℕ} (Gr : SimpleGraph (Fin n))
    (W Wt U : Matrix (Fin n) (Fin n) ℝ) (f : Fin n → EuclideanSpace ℝ (Fin p) → ℝ) (α : ℝ)
    (hA1 : MixingAssumption Gr W Wt)
    (hUs : Uᵀ = U) (hUpsd : U.PosSemidef) (hU2 : U * U = Wt - W)
    (x0 : Stack n p) (ρ : ℝ) (hρ : 1 < ρ) :
    let x := extraIter α W Wt f x0
    let q := qSeq U x
    ∀ k : ℕ,
      zNormSq Wt (q k - q (k + 1)) (x k - x (k + 1)) =
          frob (q k - q (k + 1)) (q k - q (k + 1)) + mnormSq Wt (x k - x (k + 1)) ∧
        zNormSq Wt (q k - q (k + 1)) (x k - x (k + 1)) =
          mnormSq (Wt - W) (x (k + 1)) +
            mnormSq Wt (mix (1 - Wt) (x k) + mix U (q k) + α • gradF f (x k)) ∧
        mnormSq (Wt - W) (x (k + 1)) + 1 / ρ * mnormSq Wt (mix U (q k) + α • gradF f (x k))
            - 1 / (ρ - 1) * mnormSq Wt (mix (1 - Wt) (x k)) ≤
          zNormSq Wt (q k - q (k + 1)) (x k - x (k + 1)) := by sorry

end ExtraConsensus.Sublinear
