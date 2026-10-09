-- Prove2me | Theorems.Thm_ExtraConsensus_Sublinear_theorem_3_5
-- name    : ExtraConsensus.Sublinear.theorem_3_5
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T08:19:25.331765+00:00
-- url     : https://prove2.me/theorems/95f9d3e1-8f07-4639-968c-713c8144bc42
-- title:
--   Theorem 3.5, p. 13 — for 0 < α < 2λmin(W̃)/L_f, running averages of the progress and optimality residuals are O(1/k), running minima o(1/k)
-- statement:
--   Assume Assumptions 1–3 and let $U=U^{\mathsf T}\succeq0$ with $U^2=\tilde W-W$. Let the step size satisfy $0<\alpha<2\lambda_{\min}(\tilde W)/L_{\mathbf f}$, let $\mathbf x^k$ be the EXTRA iterates from any $\mathbf x^0\in\mathbb R^{n\times p}$, $\mathbf q^k=\sum_{t=0}^kU\mathbf x^t$, $\mathbf z^k=(\mathbf q^k;\mathbf x^k)$ and $G=\operatorname{diag}(I,\tilde W)$. Then, as $k\to\infty$:
--
--   1. (running-average progress) $\displaystyle\frac1k\sum_{t=1}^k\|\mathbf z^t-\mathbf z^{t+1}\|_G^2=O\!\left(\frac1k\right)$;
--   2. (running-best progress) $\displaystyle\min_{t\le k}\big\{\|\mathbf z^t-\mathbf z^{t+1}\|_G^2\big\}=o\!\left(\frac1k\right)$;
--   3. (running-average optimality residuals)
--   $$\frac1k\sum_{t=1}^k\|U\mathbf q^t+\alpha\nabla\mathbf f(\mathbf x^t)\|_{\tilde W}^2=O\!\left(\frac1k\right)\quad\text{and}\quad\frac1k\sum_{t=1}^k\|U\mathbf x^t\|_F^2=O\!\left(\frac1k\right);$$
--   4. (running-best optimality residuals)
--   $$\min_{t\le k}\big\{\|U\mathbf q^t+\alpha\nabla\mathbf f(\mathbf x^t)\|_{\tilde W}^2\big\}=o\!\left(\frac1k\right)\quad\text{and}\quad\min_{t\le k}\big\{\|U\mathbf x^t\|_F^2\big\}=o\!\left(\frac1k\right).$$
--
--   The quantities $\|U\mathbf q^t+\alpha\nabla\mathbf f(\mathbf x^t)\|_{\tilde W}^2$ and $\|U\mathbf x^t\|_F^2$ measure the violation of the optimality conditions (3.1) and (3.2) of Lemma 3.1, i.e. of first-order optimality and of consensus. The theorem is the sublinear rate of EXTRA for convex objectives with Lipschitz gradients.
--
--   **Formalization Note** The step-size condition is multiplied out as $\alpha L_{\mathbf f}<2\lambda_{\min}(\tilde W)$ with $\lambda_{\min}(\tilde W)$ pinned down as the smallest eigenvalue. $O$ and $o$ are Landau symbols along $k\to\infty$ in $\mathbb N$; the running minima range over $1\le t\le k$, the indices of the sums. The statement concerns only the iterates: it involves no optimal pair, no $\zeta$ and no summability hypothesis.
-- source:
--   Shi, Ling, Wu & Yin, arXiv:1404.6264v4, Theorem 3.5, p. 13

import Mathlib
import Definitions.Def_ExtraConsensus_Sublinear_Model

namespace ExtraConsensus.Sublinear

open Matrix Filter Topology Asymptotics

/-- Theorem 3.5, p. 13 (goal). Under Assumptions 1–3 and `0 < α < 2λmin(W̃)/L_𝐟` (multiplied out:
`α L_𝐟 < 2λmin(W̃)`), let `𝐱ᵏ` be the EXTRA iterates from any `𝐱⁰`, `𝐪ᵏ = Σ_{t≤k} U𝐱ᵗ`,
`aₜ = ‖𝐳ᵗ − 𝐳ᵗ⁺¹‖²_G`, `bₜ = ‖U𝐪ᵗ + α∇𝐟(𝐱ᵗ)‖²_{W̃}` and `cₜ = ‖U𝐱ᵗ‖²_F`. Then
(1) `(1/k) Σ_{t=1}^k aₜ = O(1/k)`; (2) `min_{t≤k} aₜ = o(1/k)`;
(3) `(1/k) Σ_{t=1}^k bₜ = O(1/k)` and `(1/k) Σ_{t=1}^k cₜ = O(1/k)`;
(4) `min_{t≤k} bₜ = o(1/k)` and `min_{t≤k} cₜ = o(1/k)`; the minima range over `1 ≤ t ≤ k`. -/
theorem theorem_3_5 {n p : ℕ} (hn : 0 < n) (Gr : SimpleGraph (Fin n))
    (W Wt U : Matrix (Fin n) (Fin n) ℝ) (f : Fin n → EuclideanSpace ℝ (Fin p) → ℝ)
    (Lf α lmin : ℝ)
    (hA1 : MixingAssumption Gr W Wt) (hA2 : ConvexLipschitzGrad f Lf) (hA3 : SolutionExists f)
    (hUs : Uᵀ = U) (hUpsd : U.PosSemidef) (hU2 : U * U = Wt - W)
    (hlmin : IsLamMin Wt lmin) (hα0 : 0 < α) (hα : α * Lf < 2 * lmin) (x0 : Stack n p) :
    let x := extraIter α W Wt f x0
    let q := qSeq U x
    let a : ℕ → ℝ := fun t => zNormSq Wt (q t - q (t + 1)) (x t - x (t + 1))
    let b : ℕ → ℝ := fun t => mnormSq Wt (mix U (q t) + α • gradF f (x t))
    let c : ℕ → ℝ := fun t => frob (mix U (x t)) (mix U (x t))
    ((fun k : ℕ => (1 / (k : ℝ)) * ∑ t ∈ Finset.Icc 1 k, a t) =O[atTop]
        (fun k : ℕ => (1 : ℝ) / k)) ∧
      ((fun k : ℕ => runMin a k) =o[atTop] (fun k : ℕ => (1 : ℝ) / k)) ∧
      ((fun k : ℕ => (1 / (k : ℝ)) * ∑ t ∈ Finset.Icc 1 k, b t) =O[atTop]
        (fun k : ℕ => (1 : ℝ) / k)) ∧
      ((fun k : ℕ => (1 / (k : ℝ)) * ∑ t ∈ Finset.Icc 1 k, c t) =O[atTop]
        (fun k : ℕ => (1 : ℝ) / k)) ∧
      ((fun k : ℕ => runMin b k) =o[atTop] (fun k : ℕ => (1 : ℝ) / k)) ∧
      ((fun k : ℕ => runMin c k) =o[atTop] (fun k : ℕ => (1 : ℝ) / k)) := by sorry

end ExtraConsensus.Sublinear
