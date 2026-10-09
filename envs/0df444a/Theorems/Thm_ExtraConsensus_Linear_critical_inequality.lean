-- Prove2me | Theorems.Thm_ExtraConsensus_Linear_critical_inequality
-- name    : ExtraConsensus.Linear.critical_inequality
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T09:15:46.960118+00:00
-- url     : https://prove2.me/theorems/b01fb06b-50e4-45fe-8672-7c49d208ada2
-- title:
--   (3.30) under (3.38)–(3.39), pp. 16–17 — the critical inequality ‖x^{k+1}−x*‖²_{…} + ‖z^k−z^{k+1}‖²_G − (αL_f²/η)‖x^k−x^{k+1}‖²_F ≥ δ‖z^{k+1}−z*‖²_G
-- statement:
--   Under Assumptions 1–3, with $U=(\tilde W-W)^{1/2}$ and $\alpha>0$, let $x^*$ solve (1.1), $\mathbf x^*=\mathbf 1(x^*)^{\mathsf T}$, $\mathbf q^*=U\mathbf p$ satisfy (3.1)–(3.2), and $\mathbf z^k=(\mathbf q^k;\mathbf x^k)$, $\mathbf z^*=(\mathbf q^*;\mathbf x^*)$, $G=\operatorname{diag}(I,\tilde W)$. Let $\mu_{\mathbf g}>0$, and suppose (3.39):
--   $$
--   \eta\in(0,2\mu_{\mathbf g})\quad\text{and}\quad \alpha L_{\mathbf f}^2<\eta\,\lambda_{\min}(\tilde W).
--   $$
--   Let $\theta>1$ and let $\delta>0$ satisfy (3.38),
--   $$
--   \delta\le\min\left\{\frac{\alpha(2\mu_{\mathbf g}-\eta)\tilde\lambda_{\min}(\tilde W-W)}{\theta(\sigma_{\max}(I+W-2\tilde W)+\alpha L_{\mathbf f})^2+\lambda_{\max}(\tilde W)\tilde\lambda_{\min}(\tilde W-W)},\ \frac{(\theta-1)(\eta\lambda_{\min}(\tilde W)-\alpha L_{\mathbf f}^2)\tilde\lambda_{\min}(\tilde W-W)}{\theta\eta(\sigma_{\max}(\tilde W)+\alpha L_{\mathbf f})^2}\right\}.
--   $$
--   Then the critical inequality (3.30) holds for every $k$:
--   $$
--   \|\mathbf x^{k+1}-\mathbf x^*\|^2_{\alpha(2\mu_{\mathbf g}-\eta)I-(\tilde W-W)+2(I+W-2\tilde W)}+\|\mathbf z^k-\mathbf z^{k+1}\|_G^2-\frac{\alpha L_{\mathbf f}^2}{\eta}\|\mathbf x^k-\mathbf x^{k+1}\|_F^2\ \ge\ \delta\|\mathbf z^{k+1}-\mathbf z^*\|_G^2 .
--   $$
--   Combined with (3.29) this gives $\|\mathbf z^k-\mathbf z^*\|_G^2\ge(1+\delta)\|\mathbf z^{k+1}-\mathbf z^*\|_G^2$, the Q-linear contraction of Theorem 3.7; the page obtains it through (3.31), (3.35), (3.36) and (3.37).
--
--   **Formalization Note** $\lambda_{\min},\lambda_{\max},\tilde\lambda_{\min}$ and $\sigma_{\max}$ are pinned by their characterisations. The restricted strong convexity of $\mathbf g$ is not a hypothesis: this step uses $\mu_{\mathbf g}$ only as a number. Both denominators of (3.38) are positive under the hypotheses. Since $\tilde\lambda_{\min}$ exists only for $\tilde W\ne W$, the hypotheses force $n\ge2$.
-- source:
--   Shi, Ling, Wu & Yin, arXiv:1404.6264v4, proof of Theorem 3.7, "A critical inequality" (3.30) and "Establishing (3.31), Step 2" (3.36)–(3.39), pp. 16–17

import Mathlib
import Definitions.Def_ExtraConsensus_Linear_Model

namespace ExtraConsensus.Linear

open Matrix

/-- Shi–Ling–Wu–Yin, arXiv:1404.6264v4, "A critical inequality" (3.30) with (3.37)–(3.39), pp. 16–17
(proof of Theorem 3.7): if `η ∈ (0, 2μ_𝐠)`, `αL_𝐟² < ηλmin(W̃)`, `θ > 1` and `0 < δ ≤` the minimum (3.38),
then for every `k`,
`‖𝐱^{k+1} − 𝐱*‖²_{α(2μ_𝐠−η)I−(W̃−W)+2(I+W−2W̃)} + ‖𝐳ᵏ − 𝐳^{k+1}‖²_G − (αL_𝐟²/η)‖𝐱ᵏ − 𝐱^{k+1}‖²_F
  ≥ δ‖𝐳^{k+1} − 𝐳*‖²_G`. -/
theorem critical_inequality {n p : ℕ} (hn : 0 < n) (Gr : SimpleGraph (Fin n))
    (W Wt U : Matrix (Fin n) (Fin n) ℝ) (f : Fin n → EuclideanSpace ℝ (Fin p) → ℝ) (Lf α μg η : ℝ)
    (hA1 : MixingAssumption Gr W Wt) (hA2 : ExtraConsensus.Sublinear.ConvexLipschitzGrad f Lf) (hA3 : ExtraConsensus.Sublinear.SolutionExists f)
    (hUs : Uᵀ = U) (hUpsd : U.PosSemidef) (hU2 : U * U = Wt - W)
    (hα0 : 0 < α)
    (xs : EuclideanSpace ℝ (Fin p)) (hsol : ∀ y, ExtraConsensus.Sublinear.fbar f xs ≤ ExtraConsensus.Sublinear.fbar f y)
    (qs : ExtraConsensus.Sublinear.Stack n p) (hopt : ExtraConsensus.Sublinear.IsOptimalPair U α f qs (fun _ => xs))
    (hμ : 0 < μg) (hη0 : 0 < η) (hη : η < 2 * μg)
    (lmin : ℝ) (hlmin : ExtraConsensus.Sublinear.IsLamMin Wt lmin) (lmax : ℝ) (hlmax : IsLamMax Wt lmax)
    (hS : α * Lf ^ 2 < η * lmin)
    (s1 : ℝ) (hs1 : IsSigmaMax (1 + W - (2 : ℝ) • Wt) s1)
    (s2 : ℝ) (hs2 : IsSigmaMax Wt s2)
    (lt : ℝ) (hlt : IsLamMinNZ (Wt - W) lt)
    (θ : ℝ) (hθ : 1 < θ)
    (δ : ℝ) (hδ0 : 0 < δ)
    (hδ : δ ≤ min (α * (2 * μg - η) * lt / (θ * (s1 + α * Lf) ^ 2 + lmax * lt))
      ((θ - 1) * (η * lmin - α * Lf ^ 2) * lt / (θ * η * (s2 + α * Lf) ^ 2)))
    (x0 : ExtraConsensus.Sublinear.Stack n p) :
    let x := ExtraConsensus.Sublinear.extraIter α W Wt f x0
    let q := ExtraConsensus.Sublinear.qSeq U x
    let Xs : ExtraConsensus.Sublinear.Stack n p := fun _ => xs
    ∀ k : ℕ,
      δ * ExtraConsensus.Sublinear.zNormSq Wt (q (k + 1) - qs) (x (k + 1) - Xs)
        ≤ ExtraConsensus.Sublinear.mnormSq ((α * (2 * μg - η)) • (1 : Matrix (Fin n) (Fin n) ℝ) - (Wt - W)
            + (2 : ℝ) • (1 + W - (2 : ℝ) • Wt)) (x (k + 1) - Xs)
          + ExtraConsensus.Sublinear.zNormSq Wt (q k - q (k + 1)) (x k - x (k + 1))
          - α * Lf ^ 2 / η * ExtraConsensus.Sublinear.frob (x k - x (k + 1)) (x k - x (k + 1)) := by sorry

end ExtraConsensus.Linear
