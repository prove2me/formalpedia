-- Prove2me | Theorems.Thm_AdaptiveStepIPM_PredCorr_equations_4_5
-- name    : AdaptiveStepIPM.PredCorr.equations_4_5
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T15:24:41.094439+00:00
-- url     : https://prove2.me/theorems/50c6f551-806e-4e2d-afd2-fee57b19a656
-- title:
--   Equations (4)–(5) — duality measure and centrality along a step
-- statement:
--   Let $n\ge1$, let $x,s$ be strictly positive, and let $(d_x,d_y,d_s)$ solve the primal-dual direction system (2) at $(x,s)$ with parameter $\gamma$. For any real step $\theta$, write $x(\theta)=x+\theta d_x$ and $s(\theta)=s+\theta d_s$. Then
--
--   $$\mu(\theta)=(1-\theta)\mu+\theta\gamma\mu,\qquad X(\theta)s(\theta)-\mu(\theta)e=(1-\theta)(Xs-\mu e)+\theta^2D_xd_s.$$
--
--   Here $D_x=\operatorname{diag}(d_x)$, while $X(\theta)=\operatorname{diag}(x(\theta))$. The identities expose the second-order term that controls both algorithmic steps.
-- source:
--   Mizuno, Todd, Ye, On adaptive-step primal-dual interior-point algorithms for linear programming, Cornell ORIE Technical Report No. 944 (1990, rev. 1991), p. 4, equations (4)–(5)

import Mathlib
import Definitions.Def_AdaptiveStepIPM_PredCorr_Direction

open Matrix

namespace AdaptiveStepIPM.PredCorr

/-- Equations (4) and (5), printed p. 4. -/
theorem equations_4_5 {m n : ℕ} (hn : 1 ≤ n)
    (A : Matrix (Fin m) (Fin n) ℝ) (x s dx ds : Fin n → ℝ)
    (dy : Fin m → ℝ) (γ θ : ℝ)
    (hx : ∀ j, 0 < x j) (hs : ∀ j, 0 < s j)
    (hd : SearchDirection A x s γ dx dy ds) :
    mu (stepX x dx θ) (stepS s ds θ) =
      (1 - θ) * mu x s + θ * γ * mu x s ∧
    (fun j => stepX x dx θ j * stepS s ds θ j -
      mu (stepX x dx θ) (stepS s ds θ)) =
      (fun j => (1 - θ) * (x j * s j - mu x s) + θ ^ 2 * (dx j * ds j)) := by sorry

end AdaptiveStepIPM.PredCorr
