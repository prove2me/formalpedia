-- Prove2me | Theorems.Thm_BSUMConv_BSCA_eq_32
-- name    : BSUMConv.BSCA.eq_32
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T01:26:46.792793+00:00
-- url     : https://prove2.me/theorems/27f3ec5d-5543-4502-8f02-cb1a03454c94
-- title:
--   (32), p. 17 — an Armijo backtracking index exists
-- statement:
--   Let $f$ be continuously differentiable, $x$ a point, and $d$ a strict descent direction, $f'(x;d)<0$. For $0<\sigma<1$, $0<\beta<1$ and $\alpha^{\rm init}>0$, there is a nonnegative integer $j$ such that $\alpha=\alpha^{\rm init}\beta^j$ satisfies
--   $$f(x)-f(x+\alpha d)\ge-\sigma\alpha f'(x;d).$$
--
--   Thus geometric backtracking has an acceptable index whenever the direction gives strict descent.
--
--   **Formalization Note** The claim is stated at one point and direction, the form used at every BSCA iteration. The paper's condition $f'(x^r;d^r)\ne0$ is strict negativity here because (31) gives nonpositivity.
-- source:
--   Razaviyayn, Hong & Luo, arXiv:1209.2385v1, p. 17, (32)

import Mathlib
import Definitions.Def_BSUMConv_BSCA_Setting

namespace BSUMConv.BSCA

/-- Display (32), p. 17: backtracking reaches an Armijo-admissible step along a strict descent direction. -/
theorem eq_32 {N : ℕ} {n : Fin N → ℕ}
    (f : TsengBCD.Stationary.X n → ℝ) (hf : ContDiff ℝ 1 f)
    (x d : TsengBCD.Stationary.X n)
    (σ β αinit : ℝ) (hσ0 : 0 < σ) (hσ1 : σ < 1)
    (hβ0 : 0 < β) (hβ1 : β < 1) (hα : 0 < αinit)
    (hdesc : fderiv ℝ f x d < 0) :
    ∃ j : ℕ,
      let α := αinit * β ^ j
      f x - f (x + α • d) ≥ -σ * α * fderiv ℝ f x d := by sorry

end BSUMConv.BSCA
