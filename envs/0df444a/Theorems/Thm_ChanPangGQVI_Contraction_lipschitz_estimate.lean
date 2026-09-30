-- Prove2me | Theorems.Thm_ChanPangGQVI_Contraction_lipschitz_estimate
-- name    : ChanPangGQVI.Contraction.lipschitz_estimate
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-27T21:04:16.59911+00:00
-- url     : https://prove2.me/theorems/f7ac5434-fd7e-435f-89d8-a1754f26c616
-- title:
--   Lipschitz estimate for $F_\lambda$: $\|F_\lambda(y^1)-F_\lambda(y^2)\|\le[\alpha+(\lambda^2\beta^2+2\lambda(\alpha\beta-\delta)+1+\alpha^2-2\gamma)^{1/2}]\|y^1-y^2\|$
-- statement:
--   Work in $\mathbb R^n$ with the Euclidean norm and inner product. Let $\tilde K$ be a nonempty closed convex set, and let $m,f:\mathbb R^n\to\mathbb R^n$ satisfy, for all $x,y$,
--
--   1. $\|m(x)-m(y)\|\le\alpha\|x-y\|$ and $\|f(x)-f(y)\|\le\beta\|x-y\|$ (Lipschitz continuity with constants $\alpha,\beta$);
--   2. $(x-y)^T(f(x)-f(y))\ge\delta\|x-y\|^2$ and $(x-y)^T(m(x)-m(y))\ge\gamma\|x-y\|^2$ (strong monotonicity with constants $\delta,\gamma$).
--
--   Let $K(x)=m(x)+\tilde K$ and $F_\lambda(x)=P_{K(x)}(x-\lambda f(x))$. Then for every $\lambda>0$ and all vectors $y^1,y^2$,
--
--   $$
--   \|F_\lambda(y^1)-F_\lambda(y^2)\|\le\Bigl[\alpha+\bigl(\lambda^2\beta^2+2\lambda(\alpha\beta-\delta)+(1+\alpha^2-2\gamma)\bigr)^{1/2}\Bigr]\,\|y^1-y^2\| .
--   $$
--
--   This is the quantitative core of Theorem 5.3: $F_\lambda$ is Lipschitz with the bracketed constant, which is below $1$ exactly under the step-size condition of Theorem 5.3.
--
--   **Formalization Note** No sign conditions are imposed on $\alpha,\beta,\gamma,\delta$, as in the paper, and the step-size condition of Theorem 5.3 is not assumed. The square root is `Real.sqrt`; for $n\ge1$ the radicand is nonnegative under the hypotheses (it bounds a squared ratio of norms), so this is the paper's square root; for $n=0$ both sides vanish.
-- source:
--   Chan and Pang, The generalized quasi-variational inequality problem, Math. Oper. Res. 7 (1982), p. 221, §5, proof of Theorem 5.3, last display

import Mathlib
import Definitions.Def_ChanPangGQVI_Contraction_ProjectionMap

open scoped RealInnerProductSpace

namespace ChanPangGQVI.Contraction

/-- Chan and Pang 1982, §5, proof of Theorem 5.3, last display (p. 221). Under the hypotheses of
Theorem 5.3 (`K̃` nonempty, closed and convex; `m`, `f` Lipschitz with constants `α`, `β` and
strongly monotone with constants `γ`, `δ`, all in the Euclidean norm and inner product), for
every `λ > 0` and all vectors `y¹`, `y²`,
`‖F_λ(y¹) - F_λ(y²)‖ ≤ [α + (λ²β² + 2λ(αβ - δ) + (1 + α² - 2γ))^{1/2}] ‖y¹ - y²‖`.
The condition on `λ` of Theorem 5.3 is not assumed. The radicand is nonnegative whenever
`n ≥ 1` (it bounds a squared norm ratio), so `Real.sqrt` is the paper's square root. -/
theorem lipschitz_estimate {n : ℕ}
    (m f : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))
    (Ktil : Set (EuclideanSpace ℝ (Fin n)))
    (hK_ne : Ktil.Nonempty) (hK_closed : IsClosed Ktil) (hK_convex : Convex ℝ Ktil)
    (α β γ δ : ℝ)
    (hm_lip : ∀ x y, ‖m x - m y‖ ≤ α * ‖x - y‖)
    (hf_lip : ∀ x y, ‖f x - f y‖ ≤ β * ‖x - y‖)
    (hf_mono : ∀ x y, δ * ‖x - y‖ ^ 2 ≤ ⟪x - y, f x - f y⟫)
    (hm_mono : ∀ x y, γ * ‖x - y‖ ^ 2 ≤ ⟪x - y, m x - m y⟫)
    (lam : ℝ) (hlam : 0 < lam) (y₁ y₂ : EuclideanSpace ℝ (Fin n)) :
    ‖Flam m f Ktil lam y₁ - Flam m f Ktil lam y₂‖ ≤
      (α + Real.sqrt (lam ^ 2 * β ^ 2 + 2 * lam * (α * β - δ) + (1 + α ^ 2 - 2 * γ))) *
        ‖y₁ - y₂‖ := by sorry

end ChanPangGQVI.Contraction
