-- Prove2me | Theorems.Thm_ErrBoundCplx_ISTA_lemma_10_kl
-- name    : ErrBoundCplx.ISTA.lemma_10_kl
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T21:09:48.898867+00:00
-- url     : https://prove2.me/theorems/9ec9daed-587f-4626-808c-2b229b737148
-- title:
--   Lemma 10, KL consequence — under the error bound (9), f − min f is KL on the ℓ1 ball with φ(s) = √(2s/γ_R)
-- statement:
--   Let $\mu > 0$, $A \in \mathbb R^{m\times n}$, $d \in \mathbb R^m$, $f(x) = \mu\|x\|_1 + \frac12\|Ax - d\|^2$ and $S = \operatorname{argmin} f$. Fix $R > \|d\|^2/(2\mu)$ and let $\gamma_R > 0$ be such that the error bound (9) holds:
--   $$f(x) - \min f \ge 2\gamma_R\operatorname{dist}^2(x, S) \qquad \text{whenever } \|x\|_1 \le R.$$
--   Put $\varphi(s) = \sqrt{2\gamma_R^{-1} s}$. Then, for every $\bar r > 0$:
--   1. $\varphi \in \mathcal K(0, \bar r)$: $\varphi$ is continuous and concave on $[0, \bar r)$, nonnegative, $\varphi(0) = 0$, $C^1$ on $(0, \bar r)$ with $\varphi' > 0$;
--   2. $f - \min f$ has the KL property on $\{x : \|x\|_1 \le R\} \cap [0 < f - \min f < \bar r]$ with desingularizing function $\varphi$: for every such $x$ and every $v \in \partial f(x)$,
--   $$\varphi'(f(x) - \min f)\,\|v\| \ge 1.$$
--
--   This is the sentence "as a consequence $f$ is a KL function on the $\ell^1$ ball of radius $R$ and admits $\varphi(s) = \sqrt{2\gamma_R^{-1}s}$ as desingularizing function", stated for every $\gamma_R$ satisfying (9), in particular for the value (10). Its inverse is $\psi(s) = \frac{\gamma_R}{2}s^2$, the case treated by Corollary 20.
--
--   **Formalization Note** "KL function on the ball" is read as the KL inequality at every point of the ball where $0 < f - \min f < \bar r$, for every $\bar r > 0$ (a global desingularizing function). The subdifferential is the convex one, `subgrad` applied to $f - \min f$ viewed in `EReal` (it equals $\partial f$). $\mathcal K(0,\bar r)$ is the published `IsDesingularizer`.
-- source:
--   arXiv:1510.08234v3, Lemma 10, last sentence, p. 12; K(0, r₀), §2.3, p. 6

import Mathlib
import Definitions.Def_MoreauProx_Characterization_GammaZero
import Definitions.Def_NonconvexSplitting_ADMMKL_KLProperty
import Definitions.Def_BoydADMM_Prox_Basic
import Definitions.Def_ErrBoundCplx_ISTA_DescentSeq
import Definitions.Def_ErrBoundCplx_ISTA_Lasso
open MoreauProx.Characterization NonconvexSplitting.ADMMKL BoydADMM.Prox

namespace ErrBoundCplx.ISTA

/-- arXiv:1510.08234v3, Lemma 10, last sentence, p. 12 ("As a consequence f is a KL function on
the ℓ1 ball of radius R and admits φ(s) = √(2γ_R⁻¹ s) as desingularizing function"), for any
`γ_R > 0` satisfying the error bound (9). Let `μ > 0`, `R > ‖d‖²/(2μ)` and `γ_R > 0` with
`f(x) − min f ≥ 2γ_R dist²(x, S)` whenever `‖x‖₁ ≤ R`. Put `φ(s) = √(2s/γ_R)`. Then for every
`r̄ > 0`, `φ ∈ K(0, r̄)` and `f − min f` has the KL property with desingularizing function `φ`
on `{‖x‖₁ ≤ R} ∩ [0 < f − min f < r̄]`. -/
theorem lemma_10_kl {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ)
    (d : EuclideanSpace ℝ (Fin m)) (μ : ℝ) (hμ : 0 < μ)
    (R : ℝ) (hR : ‖d‖ ^ 2 / (2 * μ) < R) (γR : ℝ) (hγ : 0 < γR)
    (hEB : ∀ x : EuclideanSpace ℝ (Fin n), l1Norm x ≤ R →
      2 * γR * Metric.infDist x (lassoArgmin A d μ) ^ 2 ≤ lassoObj A d μ x - lassoMin A d μ) :
    let φ : ℝ → ℝ := fun s => Real.sqrt (2 * s / γR)
    ∀ rbar : ℝ, 0 < rbar →
      IsDesingularizer rbar φ ∧
      KLOnSet (fun z => ((lassoObj A d μ z - lassoMin A d μ : ℝ) : EReal))
        {x | l1Norm x ≤ R} rbar φ := by sorry

end ErrBoundCplx.ISTA
