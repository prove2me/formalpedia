-- Prove2me | Theorems.Thm_ExtraConsensus_Linear_eq_3_29
-- name    : ExtraConsensus.Linear.eq_3_29
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T09:15:38.111153+00:00
-- url     : https://prove2.me/theorems/16cc1d92-9254-401c-b3bc-dcdd6de41d84
-- title:
--   Eq. (3.29), p. 16 — ‖z^k − z*‖²_G − ‖z^{k+1} − z*‖²_G ≥ ‖x^{k+1} − x*‖²_{α(2μ_g−η)I−(W̃−W)+2(I+W−2W̃)} + ‖z^k − z^{k+1}‖²_G − (αL_f²/η)‖x^k − x^{k+1}‖²_F
-- statement:
--   Under Assumptions 1–3, with $U=(\tilde W-W)^{1/2}$ and step size $\alpha>0$, let $x^*$ solve (1.1), $\mathbf x^*=\mathbf 1(x^*)^{\mathsf T}$, and let $\mathbf q^*=U\mathbf p$ satisfy (3.1)–(3.2) with $\mathbf x^*$. Write $\mathbf z^k=(\mathbf q^k;\mathbf x^k)$, $\mathbf z^*=(\mathbf q^*;\mathbf x^*)$ and $G=\operatorname{diag}(I,\tilde W)$. Suppose $\mathbf g(\mathbf x)=\mathbf f(\mathbf x)+\frac1{4\alpha}\|\mathbf x\|^2_{\tilde W-W}$ is restricted strongly convex with respect to $\mathbf x^*$ with constant $\mu_{\mathbf g}>0$, and let $\eta>0$ be a tunable parameter. Then for every $k$
--   $$
--   \|\mathbf z^k-\mathbf z^*\|_G^2-\|\mathbf z^{k+1}-\mathbf z^*\|_G^2\ \ge\ \|\mathbf x^{k+1}-\mathbf x^*\|^2_{\alpha(2\mu_{\mathbf g}-\eta)I-(\tilde W-W)+2(I+W-2\tilde W)}+\|\mathbf z^k-\mathbf z^{k+1}\|_G^2-\frac{\alpha L_{\mathbf f}^2}{\eta}\|\mathbf x^k-\mathbf x^{k+1}\|_F^2 .
--   $$
--   This is the per-step descent inequality of the proof of Theorem 3.7: it lower-bounds the decrease of the $G$-distance to $\mathbf z^*$, and Theorem 3.7 follows once the right-hand side dominates $\delta\|\mathbf z^{k+1}-\mathbf z^*\|_G^2$.
--
--   **Formalization Note** The subscript matrix may be indefinite; $\|\mathbf y\|_M^2$ denotes the quadratic form $\operatorname{trace}(\mathbf y^{\mathsf T}M\mathbf y)$, as on the page. The page's sentence introducing (3.29) lacks the closing bracket of $2\langle\mathbf z^{k+1}-\mathbf z^k,G(\mathbf z^*-\mathbf z^{k+1})\rangle$; this does not affect the statement.
-- source:
--   Shi, Ling, Wu & Yin, arXiv:1404.6264v4, proof of Theorem 3.7, eq. (3.29), p. 16 (with η > 0 from (3.25), p. 15)

import Mathlib
import Definitions.Def_ExtraConsensus_Linear_Model

namespace ExtraConsensus.Linear

open Matrix

/-- Shi–Ling–Wu–Yin, arXiv:1404.6264v4, eq. (3.29), p. 16 (proof of Theorem 3.7): if `𝐠` is
restricted strongly convex at `𝐱* = 𝟏(x*)ᵀ` with constant `μ_𝐠`, then for every `η > 0` and every `k`,
`‖𝐳ᵏ − 𝐳*‖²_G − ‖𝐳^{k+1} − 𝐳*‖²_G ≥ ‖𝐱^{k+1} − 𝐱*‖²_{α(2μ_𝐠−η)I−(W̃−W)+2(I+W−2W̃)}
  + ‖𝐳ᵏ − 𝐳^{k+1}‖²_G − (αL_𝐟²/η)‖𝐱ᵏ − 𝐱^{k+1}‖²_F`. -/
theorem eq_3_29 {n p : ℕ} (hn : 0 < n) (Gr : SimpleGraph (Fin n))
    (W Wt U : Matrix (Fin n) (Fin n) ℝ) (f : Fin n → EuclideanSpace ℝ (Fin p) → ℝ) (Lf α μg η : ℝ)
    (hA1 : MixingAssumption Gr W Wt) (hA2 : ExtraConsensus.Sublinear.ConvexLipschitzGrad f Lf) (hA3 : ExtraConsensus.Sublinear.SolutionExists f)
    (hUs : Uᵀ = U) (hUpsd : U.PosSemidef) (hU2 : U * U = Wt - W)
    (hα0 : 0 < α)
    (xs : EuclideanSpace ℝ (Fin p)) (hsol : ∀ y, ExtraConsensus.Sublinear.fbar f xs ≤ ExtraConsensus.Sublinear.fbar f y)
    (qs : ExtraConsensus.Sublinear.Stack n p) (hopt : ExtraConsensus.Sublinear.IsOptimalPair U α f qs (fun _ => xs))
    (hrsc : RSCAtStack (gradG α W Wt f) (fun _ => xs) μg)
    (hη : 0 < η) (x0 : ExtraConsensus.Sublinear.Stack n p) :
    let x := ExtraConsensus.Sublinear.extraIter α W Wt f x0
    let q := ExtraConsensus.Sublinear.qSeq U x
    let Xs : ExtraConsensus.Sublinear.Stack n p := fun _ => xs
    ∀ k : ℕ,
      ExtraConsensus.Sublinear.mnormSq ((α * (2 * μg - η)) • (1 : Matrix (Fin n) (Fin n) ℝ) - (Wt - W)
          + (2 : ℝ) • (1 + W - (2 : ℝ) • Wt)) (x (k + 1) - Xs)
        + ExtraConsensus.Sublinear.zNormSq Wt (q k - q (k + 1)) (x k - x (k + 1))
        - α * Lf ^ 2 / η * ExtraConsensus.Sublinear.frob (x k - x (k + 1)) (x k - x (k + 1))
      ≤ ExtraConsensus.Sublinear.zNormSq Wt (q k - qs) (x k - Xs) - ExtraConsensus.Sublinear.zNormSq Wt (q (k + 1) - qs) (x (k + 1) - Xs) := by sorry

end ExtraConsensus.Linear
