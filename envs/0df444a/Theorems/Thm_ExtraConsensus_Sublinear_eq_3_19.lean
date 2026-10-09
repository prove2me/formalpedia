-- Prove2me | Theorems.Thm_ExtraConsensus_Sublinear_eq_3_19
-- name    : ExtraConsensus.Sublinear.eq_3_19
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T08:17:43.208121+00:00
-- url     : https://prove2.me/theorems/4429e359-969a-4846-9610-58b2955771ac
-- title:
--   Eq. (3.19), p. 13 — Σ_{t≥0} ‖z^t − z^{t+1}‖²_G ≤ ‖z⁰ − z*‖²_G/ζ < ∞
-- statement:
--   Under the hypotheses of Theorem 3.3 (Assumptions 1–3, $U=U^{\mathsf T}\succeq0$ with $U^2=\tilde W-W$, $0<\alpha<2\lambda_{\min}(\tilde W)/L_{\mathbf f}$), let $(\mathbf q^*,\mathbf x^*)$ satisfy (3.1)–(3.2) and $\zeta=1-\alpha L_{\mathbf f}/(2\lambda_{\min}(\tilde W))$. Then the series of progress terms converges and
--   $$\sum_{t=0}^\infty\|\mathbf z^t-\mathbf z^{t+1}\|_G^2\ \le\ \frac{\|\mathbf z^0-\mathbf z^*\|_G^2}{\zeta}<\infty .$$
--
--   Together with Proposition 3.4 this gives parts (1) and (2) of Theorem 3.5.
--
--   **Formalization Note** The printed display divides by $\delta$, has "$=$" in its first step and writes $\mathbf z_0$. The constant of (3.9) is $\zeta$ ($\delta$ belongs to Theorem 3.7), summing (3.9) gives an inequality, and $\mathbf z_0$ is $\mathbf z^0$; the statement uses $\zeta$, "$\le$" and $\mathbf z^0$. Summability is stated explicitly because a Lean `tsum` of a non-summable series is $0$.
-- source:
--   Shi, Ling, Wu & Yin, arXiv:1404.6264v4, §3.2, proof of Theorem 3.5, eq. (3.19), p. 13

import Mathlib
import Definitions.Def_ExtraConsensus_Sublinear_Model

namespace ExtraConsensus.Sublinear

open Matrix Filter Topology Asymptotics

/-- Eq. (3.19), p. 13, with the constant `ζ` of (3.9) and `≤` (see the natural-language
statement for the printed slips). Under the hypotheses of Theorem 3.3, for every pair `(𝐪*, 𝐱*)`
satisfying (3.1)–(3.2), the progress `‖𝐳ᵗ − 𝐳ᵗ⁺¹‖²_G` is summable and
`Σ_{t=0}^∞ ‖𝐳ᵗ − 𝐳ᵗ⁺¹‖²_G ≤ ‖𝐳⁰ − 𝐳*‖²_G / ζ`, `ζ = 1 − αL_𝐟/(2λmin(W̃))`. -/
theorem eq_3_19 {n p : ℕ} (hn : 0 < n) (Gr : SimpleGraph (Fin n))
    (W Wt U : Matrix (Fin n) (Fin n) ℝ) (f : Fin n → EuclideanSpace ℝ (Fin p) → ℝ)
    (Lf α lmin : ℝ)
    (hA1 : MixingAssumption Gr W Wt) (hA2 : ConvexLipschitzGrad f Lf) (hA3 : SolutionExists f)
    (hUs : Uᵀ = U) (hUpsd : U.PosSemidef) (hU2 : U * U = Wt - W)
    (hlmin : IsLamMin Wt lmin) (hα0 : 0 < α) (hα : α * Lf < 2 * lmin) (x0 : Stack n p)
    (qs xs : Stack n p) (hopt : IsOptimalPair U α f qs xs) :
    let x := extraIter α W Wt f x0
    let q := qSeq U x
    Summable (fun t : ℕ => zNormSq Wt (q t - q (t + 1)) (x t - x (t + 1))) ∧
      ∑' t : ℕ, zNormSq Wt (q t - q (t + 1)) (x t - x (t + 1)) ≤
        zNormSq Wt (q 0 - qs) (x 0 - xs) / (1 - α * Lf / (2 * lmin)) := by sorry

end ExtraConsensus.Sublinear
