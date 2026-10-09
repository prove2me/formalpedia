-- Prove2me | Theorems.Thm_ExtraConsensus_Sublinear_eq_3_17
-- name    : ExtraConsensus.Sublinear.eq_3_17
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T08:18:00.476843+00:00
-- url     : https://prove2.me/theorems/0b8cb0c6-ad79-428e-9b06-ef43166b92b5
-- title:
--   Eq. (3.17), p. 12 — 0 ≤ ‖z^k − z*‖²_G − ‖z^{k+1} − z*‖²_G − ‖z^k − z^{k+1}‖²_G − 2‖x^{k+1} − x*‖²_{I+W−2W̃} + (αL_f/2)‖x^k − x^{k+1}‖²_F
-- statement:
--   Assume Assumptions 1–3, $\alpha>0$, $U=U^{\mathsf T}\succeq0$ with $U^2=\tilde W-W$, and let $(\mathbf q^*,\mathbf x^*)$ satisfy (3.1)–(3.2). With $\mathbf x^k$ the EXTRA iterates from any $\mathbf x^0$, $\mathbf q^k=\sum_{t\le k}U\mathbf x^t$, $\mathbf z^k=(\mathbf q^k;\mathbf x^k)$, $\mathbf z^*=(\mathbf q^*;\mathbf x^*)$ and $G=\operatorname{diag}(I,\tilde W)$, for every $k\ge0$
--   $$0\le\|\mathbf z^k-\mathbf z^*\|_G^2-\|\mathbf z^{k+1}-\mathbf z^*\|_G^2-\|\mathbf z^k-\mathbf z^{k+1}\|_G^2-2\|\mathbf x^{k+1}-\mathbf x^*\|_{I+W-2\tilde W}^2+\frac{\alpha L_{\mathbf f}}2\|\mathbf x^k-\mathbf x^{k+1}\|_F^2 .$$
--
--   Combined with $I+W-2\tilde W\succeq0$ and the step-size condition, this yields the contraction (3.9) of Theorem 3.3.
--
--   **Formalization Note** $\|\cdot\|_{I+W-2\tilde W}^2$ is the quadratic form $\langle\mathbf x,(I+W-2\tilde W)\mathbf x\rangle$.
-- source:
--   Shi, Ling, Wu & Yin, arXiv:1404.6264v4, §3.2, proof of Theorem 3.3, eq. (3.17), p. 12

import Mathlib
import Definitions.Def_ExtraConsensus_Sublinear_Model

namespace ExtraConsensus.Sublinear

open Matrix Filter Topology Asymptotics

/-- Eq. (3.17), p. 12. Under Assumptions 1–3 with `α > 0`, for every pair `(𝐪*, 𝐱*)` satisfying
(3.1)–(3.2) and every `k`, with `𝐳ᵏ = (𝐪ᵏ; 𝐱ᵏ)`, `𝐳* = (𝐪*; 𝐱*)` and `G = diag(I, W̃)`:
`0 ≤ ‖𝐳ᵏ − 𝐳*‖²_G − ‖𝐳^{k+1} − 𝐳*‖²_G − ‖𝐳ᵏ − 𝐳^{k+1}‖²_G − 2‖𝐱^{k+1} − 𝐱*‖²_{I+W−2W̃}
  + (αL_𝐟/2)‖𝐱ᵏ − 𝐱^{k+1}‖²_F`. -/
theorem eq_3_17 {n p : ℕ} (hn : 0 < n) (Gr : SimpleGraph (Fin n))
    (W Wt U : Matrix (Fin n) (Fin n) ℝ) (f : Fin n → EuclideanSpace ℝ (Fin p) → ℝ)
    (Lf α lmin : ℝ)
    (hA1 : MixingAssumption Gr W Wt) (hA2 : ConvexLipschitzGrad f Lf) (hA3 : SolutionExists f)
    (hUs : Uᵀ = U) (hUpsd : U.PosSemidef) (hU2 : U * U = Wt - W)
    (hα0 : 0 < α) (x0 : Stack n p) (qs xs : Stack n p) (hopt : IsOptimalPair U α f qs xs) :
    let x := extraIter α W Wt f x0
    let q := qSeq U x
    ∀ k : ℕ,
      0 ≤ zNormSq Wt (q k - qs) (x k - xs) - zNormSq Wt (q (k + 1) - qs) (x (k + 1) - xs)
        - zNormSq Wt (q k - q (k + 1)) (x k - x (k + 1))
        - 2 * mnormSq (1 + W - (2 : ℝ) • Wt) (x (k + 1) - xs)
        + α * Lf / 2 * frob (x k - x (k + 1)) (x k - x (k + 1)) := by sorry

end ExtraConsensus.Sublinear
