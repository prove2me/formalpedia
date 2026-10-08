-- Prove2me | Theorems.Thm_DataDrivenRO_Moment_cauchy_schwarz_steps
-- name    : DataDrivenRO.Moment.cauchy_schwarz_steps
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-05T14:24:26.492926+00:00
-- url     : https://prove2.me/theorems/1feb8e96-f17b-4f00-89e1-3ce641542688
-- title:
--   EC.1.7, p. ec8 — two Euclidean ball support maximizations
-- statement:
--   Let $\Gamma_1,r\ge0$, let $C^\top C=\hat\Sigma+\Gamma_2I$ with $\Gamma_2\ge0$, and fix $v\in\mathbb R^d$. The linear functionals on the two balls of (35) attain the maxima
--
--   $$
--   \max_{\|y\|_2\le\Gamma_1}v^\top y=\Gamma_1\|v\|_2,
--   \qquad
--   \max_{\|w\|_2\le r}v^\top C^\top w=r\|Cv\|_2,
--   \qquad
--   \|Cv\|_2=\sqrt{v^\top(\hat\Sigma+\Gamma_2I)v}.
--   $$
--
--   These evaluations determine the support function of the moment uncertainty set. They include zero radii and zero vectors, where the maxima remain attained.
--
--   **Formalization Note** The two maxima are stated with `IsGreatest` on the images of the closed balls. The matrix factor $C$ need not be triangular; the source's support formula depends only on $C^\top C$.
-- source:
--   Bertsimas, Gupta & Kallus, Data-Driven Robust Optimization, arXiv:1401.0212v2, EC.1.7, proof of Theorem 10, p. ec8 (PDF p. 46)

import Mathlib
import Definitions.Def_DataDrivenRO_Moment_Setting

namespace DataDrivenRO.Moment

/-- The two Cauchy–Schwarz maximizations cited in EC.1.7, p. ec8. -/
theorem cauchy_schwarz_steps {d : ℕ} (Γ₁ Γ₂ r : ℝ)
    (Shat C : Matrix (Fin d) (Fin d) ℝ)
    (hΓ₁ : 0 ≤ Γ₁) (hΓ₂ : 0 ≤ Γ₂) (hr : 0 ≤ r)
    (hC : C.transpose * C = Shat + Γ₂ • (1 : Matrix (Fin d) (Fin d) ℝ))
    (v : Fin d → ℝ) :
    IsGreatest ((fun y : Fin d → ℝ => v ⬝ᵥ y) '' {y | enorm y ≤ Γ₁})
        (Γ₁ * enorm v) ∧
    IsGreatest ((fun w : Fin d → ℝ => v ⬝ᵥ Matrix.mulVec C.transpose w) ''
        {w | enorm w ≤ r}) (r * enorm (Matrix.mulVec C v)) ∧
    enorm (Matrix.mulVec C v) =
      Real.sqrt (v ⬝ᵥ Matrix.mulVec (Shat + Γ₂ • (1 : Matrix (Fin d) (Fin d) ℝ)) v) := by sorry

end DataDrivenRO.Moment
