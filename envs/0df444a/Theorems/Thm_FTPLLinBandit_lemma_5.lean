-- Prove2me | Theorems.Thm_FTPLLinBandit_lemma_5
-- name    : FTPLLinBandit.lemma_5
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T00:04:07.016212+00:00
-- url     : https://prove2.me/theorems/ddc3010c-2a92-46fc-afff-f0bf25ac7164
-- title:
--   Lemma 5 — $\mathcal I^v_t\preceq\max\{\lambda\|\mathcal I^v_1\|_{\mathrm{op}},(1+\chi^2(\rho_1(\cdot-v)\|\rho_1))I_\varphi\}\,\Sigma_t^{-1}$ under random weighting
-- statement:
--   Let $d\ge1$, let $\rho_1=P_{\lambda I}$ be one of the three initializers of Table 2 with $\lambda>0$, let $\varphi$ be one of the two scalar laws of Table 3, and let $\hat\theta_1,\dots,\hat\theta_{t-1}\in\mathbb R^d$. Let $\rho_t$ be the random-weighting density built from $\rho_1$, $\varphi$ and these vectors, and $\Sigma_t=\lambda I+\sum_{j=1}^{t-1}\hat\theta_j\hat\theta_j^\top$. Then for every shift $v\in\mathbb R^d$,
--   $$\mathcal I^v(\rho_t)\preceq\max\Big\{\lambda\big\|\mathcal I^v(\rho_1)\big\|_{\mathrm{op}},\ \big(1+\chi^2(\rho_1(\cdot-v)\,\|\,\rho_1)\big)I_\varphi\Big\}\,\Sigma_t^{-1},$$
--   where $I_\varphi=\int\varphi'^2/\varphi$ and $\rho_1(\cdot-v)$ is the density of $Z+v$, $Z\sim\rho_1$; that is, $u^\top\mathcal I^v(\rho_t)u\le\max\{\cdots\}\,u^\top\Sigma_t^{-1}u$ for every $u$ (vacuous when the maximum is $+\infty$).
--
--   At $v=0$ this is a matrix analogue of the Fisher information inequality for convolutions; combined with Table 2 it turns Theorem 4 into the bound of Corollary 6.
--
--   Differences from the source:
--   - encoding: the covariance matrix M_t (and matrix inequalities ⪯) → its quadratic form actCovQ (inequalities between quadratic forms in every direction); reason: a symmetric matrix is determined by its quadratic form; same instances
--   - encoding: ‖I^v_1‖_op and 1 + χ²(ρ₁(· − v)‖ρ₁), possibly infinite → sup_{‖u‖≤1} uᵀI^v(ρ₁)u and ∫ρ₁(z − v)²/ρ₁(z) dz in [0, ∞]; the maximum is taken in [0, ∞]; reason: I^v is positive semidefinite, so its operator norm is the supremum of its quadratic form on the unit ball; same instances
--   - encoding: rounds t = 1, 2, …; Θ̂_1 = 0; ρ_1, Σ_1 → rounds indexed from 0; a past list of length t gives the paper's ρ_{t+1}, Σ_{t+1}; reason: Lean convention; same instances
--   - encoding: ℝ^d with the standing d ≥ 1 → hypothesis 1 ≤ d; reason: the paper's standing assumption (§2.1, p.4)
-- source:
--   Wei, Follow the Perturbed Leader for Linear Bandits: √T Regret over General Action Sets, arXiv:2610.17818, Lemma 5, Eq. (13), p.11 (proof Appendix E.2, pp.27–29)

import Mathlib
import Definitions.Def_FTPLLinBandit_radialFn
import Definitions.Def_FTPLLinBandit_scalarDens
import Definitions.Def_FTPLLinBandit_ellDens
import Definitions.Def_FTPLLinBandit_rwDens
import Definitions.Def_FTPLLinBandit_shapeMat
import Definitions.Def_FTPLLinBandit_fisherOp
import Definitions.Def_FTPLLinBandit_chiSqPlusOne
import Definitions.Def_FTPLLinBandit_fisherScalar

open scoped ENNReal

namespace FTPLLinBandit

/-- **Lemma 5 (shifted Fisher information under random weighting).** Wei, arXiv:2610.17818,
Lemma 5, Eq. (13), p.11: "Consider random-reweighting perturbations. … Fix any λ > 0 and set
Σ_t = λI + ∑_{j=1}^{t−1} θ̂_jθ̂_jᵀ. Then, for every shift v ∈ ℝ^d,
I^v_t ⪯ max{λ‖I^v_1‖_op, (1 + χ²(ρ₁(· − v)‖ρ₁)) I_φ} Σ_t⁻¹, where I_φ = ∫ φ′(ξ)²/φ(ξ) dξ".

For every initializer `ρ₁ = P_{λI}` of Table 2 (profile `f`), every scalar law `φ` of Table 3,
`λ > 0`, past estimates `θs` (the paper's `θ̂_1, …, θ̂_{t−1}`), shift `v` and direction `u`:
`uᵀ I^v(ρ_t) u ≤ max{λ‖I^v(ρ₁)‖_op, (1 + χ²(ρ₁(· − v)‖ρ₁)) I_φ} · uᵀ Σ_t⁻¹ u`, with
`ρ_t = rwDens ρ₁ φ θs` and `Σ_t = shapeMat λ θs`.

**Formalization Note.** The matrix inequality `X ⪯ c Σ⁻¹` is stated for the quadratic forms in
every direction `u`; the information quantities and the maximum are in `[0, ∞]` (the bound is
vacuous when the maximum is `∞`). The past estimates are an arbitrary finite list. -/
theorem lemma_5 {d t : ℕ} (hd : 1 ≤ d) (f : RadialProfile) (φ : ScalarLaw) (lam : ℝ)
    (hlam : 0 < lam) (θs : Fin t → EuclideanSpace ℝ (Fin d))
    (v u : EuclideanSpace ℝ (Fin d)) :
    fisherQ (rwDens (ellDens (radialFn d f) (lam • (1 : Matrix (Fin d) (Fin d) ℝ)))
        (scalarDens φ) θs) v u ≤
      max (ENNReal.ofReal lam *
            fisherOp (ellDens (radialFn d f) (lam • (1 : Matrix (Fin d) (Fin d) ℝ))) v)
          (chiSqPlusOne (ellDens (radialFn d f) (lam • (1 : Matrix (Fin d) (Fin d) ℝ))) v *
            fisherScalar (scalarDens φ)) *
        ENNReal.ofReal (quadForm (shapeMat lam θs)⁻¹ u) := by sorry

end FTPLLinBandit
