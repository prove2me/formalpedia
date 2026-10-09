-- Prove2me | Theorems.Thm_ExtraConsensus_Sublinear_theorem_3_3
-- name    : ExtraConsensus.Sublinear.theorem_3_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T08:17:54.214076+00:00
-- url     : https://prove2.me/theorems/a4b1bc76-a16b-4e35-ac93-ad3b0540eaf9
-- title:
--   Theorem 3.3, p. 11 — for 0 < α < 2λmin(W̃)/L_f, ‖z^k − z*‖²_G − ‖z^{k+1} − z*‖²_G ≥ ζ‖z^k − z^{k+1}‖²_G and z^k → an optimal z*
-- statement:
--   Assume Assumptions 1–3, let $U=U^{\mathsf T}\succeq0$ with $U^2=\tilde W-W$, and let the step size satisfy
--   $$0<\alpha<\frac{2\lambda_{\min}(\tilde W)}{L_{\mathbf f}} .$$
--   Let $\mathbf x^k$ be the EXTRA iterates from any $\mathbf x^0$, $\mathbf q^k=\sum_{t\le k}U\mathbf x^t$, $\mathbf z^k=(\mathbf q^k;\mathbf x^k)$ and $G=\operatorname{diag}(I,\tilde W)$. Then
--
--   1. for every $\mathbf z^*=(\mathbf q^*;\mathbf x^*)$ satisfying the optimality conditions (3.1)–(3.2) and every $k=0,1,\dots$,
--   $$\|\mathbf z^k-\mathbf z^*\|_G^2-\|\mathbf z^{k+1}-\mathbf z^*\|_G^2\ \ge\ \zeta\,\|\mathbf z^k-\mathbf z^{k+1}\|_G^2,\qquad \zeta=1-\frac{\alpha L_{\mathbf f}}{2\lambda_{\min}(\tilde W)};\tag{3.9}$$
--   2. $\mathbf z^k$ converges to an optimal $\mathbf z^*=(\mathbf q^*;\mathbf x^*)$, i.e. one satisfying (3.1)–(3.2); its $\mathbf x^*$ is consensual and each of its rows solves (1.1).
--
--   This is the convergence theorem of EXTRA: with a fixed step size the local copies reach the exact minimizer, unlike decentralized gradient descent.
--
--   **Formalization Note** The step-size condition is multiplied out as $\alpha L_{\mathbf f}<2\lambda_{\min}(\tilde W)$, so that $L_{\mathbf f}=0$ is allowed (then any $\alpha>0$ qualifies). $\lambda_{\min}(\tilde W)$ is a parameter pinned down as the smallest eigenvalue of $\tilde W$. The last clause (consensus and optimality of the limit) is what "optimal" means by Lemma 3.1 and is stated explicitly.
-- source:
--   Shi, Ling, Wu & Yin, arXiv:1404.6264v4, Theorem 3.3, eq. (3.9), p. 11

import Mathlib
import Definitions.Def_ExtraConsensus_Sublinear_Model

namespace ExtraConsensus.Sublinear

open Matrix Filter Topology Asymptotics

/-- Theorem 3.3, p. 11. Under Assumptions 1–3, if `0 < α < 2λmin(W̃)/L_𝐟` (multiplied out:
`α L_𝐟 < 2λmin(W̃)`), then
1. (3.9): for every pair `𝐳* = (𝐪*; 𝐱*)` satisfying (3.1)–(3.2) and every `k`,
   `‖𝐳ᵏ − 𝐳*‖²_G − ‖𝐳^{k+1} − 𝐳*‖²_G ≥ ζ‖𝐳ᵏ − 𝐳^{k+1}‖²_G` with `ζ = 1 − αL_𝐟/(2λmin(W̃))`;
2. `𝐳ᵏ = (𝐪ᵏ; 𝐱ᵏ)` converges to an optimal `𝐳* = (𝐪*; 𝐱*)` (satisfying (3.1)–(3.2)), whose `𝐱*` is
   consensual with every row a solution of (1.1). -/
theorem theorem_3_3 {n p : ℕ} (hn : 0 < n) (Gr : SimpleGraph (Fin n))
    (W Wt U : Matrix (Fin n) (Fin n) ℝ) (f : Fin n → EuclideanSpace ℝ (Fin p) → ℝ)
    (Lf α lmin : ℝ)
    (hA1 : MixingAssumption Gr W Wt) (hA2 : ConvexLipschitzGrad f Lf) (hA3 : SolutionExists f)
    (hUs : Uᵀ = U) (hUpsd : U.PosSemidef) (hU2 : U * U = Wt - W)
    (hlmin : IsLamMin Wt lmin) (hα0 : 0 < α) (hα : α * Lf < 2 * lmin) (x0 : Stack n p) :
    let x := extraIter α W Wt f x0
    let q := qSeq U x
    (∀ qs xs : Stack n p, IsOptimalPair U α f qs xs → ∀ k : ℕ,
      (1 - α * Lf / (2 * lmin)) * zNormSq Wt (q k - q (k + 1)) (x k - x (k + 1)) ≤
        zNormSq Wt (q k - qs) (x k - xs) - zNormSq Wt (q (k + 1) - qs) (x (k + 1) - xs)) ∧
    ∃ qs xs : Stack n p, IsOptimalPair U α f qs xs ∧
      Tendsto q atTop (𝓝 qs) ∧ Tendsto x atTop (𝓝 xs) ∧
      (∀ i j, xs i = xs j) ∧ ∀ i, ∀ y, fbar f (xs i) ≤ fbar f y := by sorry

end ExtraConsensus.Sublinear
