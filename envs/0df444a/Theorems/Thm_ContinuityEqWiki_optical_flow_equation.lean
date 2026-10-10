-- Prove2me | Theorems.Thm_ContinuityEqWiki_optical_flow_equation
-- name    : ContinuityEqWiki.optical_flow_equation
-- status  : Open
-- author  : @Lucas
-- created : 2026-10-09T21:29:43.006238+00:00
-- url     : https://prove2.me/theorems/83c518be-7419-4163-9929-452ca1977efe
-- title:
--   Optical flow equation: $\nabla I\cdot\mathbf V+\partial_t I=0$
-- statement:
--   Let $I(t,x,y)$ be an image intensity, $C^1$ jointly in time $t$ and image coordinates $(x,y)\in\mathbb R^2$, and let $\mathbf V(t,x,y)=(V_x,V_y)$ be an optical flow velocity field. Let $t\mapsto p(t)\in\mathbb R^2$ be the image position of a moving object point, moving with the flow: $p'(t)=\mathbf V(t,p(t))$ for all $t$. Assume brightness constancy: $I(t,p(t))$ does not depend on $t$. Then for every $t$, at the point $(t,p(t))$,
--   $$\frac{\partial I}{\partial x}V_x+\frac{\partial I}{\partial y}V_y+\frac{\partial I}{\partial t}=\nabla I\cdot\mathbf V+\frac{\partial I}{\partial t}=0 .$$
--
--   **Formalization Note** The source's discrete assumption ("brightness of the moving object did not change between two image frames") is encoded in its continuous-time form: the intensity is constant along the trajectory of the moving point, and the equation is asserted along that trajectory.
-- source:
--   Wikipedia, "Continuity equation", revision oldid=1378634825, https://en.wikipedia.org/w/index.php?title=Continuity_equation&oldid=1378634825, section "Computer vision" (optical flow equation)

import Mathlib
import Definitions.Def_ContinuityEqWiki_Defs

namespace ContinuityEqWiki

theorem optical_flow_equation (I : ℝ → (Fin 2 → ℝ) → ℝ) (V : ℝ → (Fin 2 → ℝ) → Fin 2 → ℝ)
    (p : ℝ → Fin 2 → ℝ) (hI : ContDiff ℝ 1 (Function.uncurry I))
    (hp : ∀ t, HasDerivAt p (V t (p t)) t)
    (brightness_constancy : ∀ s t, I s (p s) = I t (p t)) :
    ∀ t, partialDeriv 0 (I t) (p t) * V t (p t) 0 + partialDeriv 1 (I t) (p t) * V t (p t) 1
      + timeDeriv I t (p t) = 0 := by sorry

end ContinuityEqWiki
