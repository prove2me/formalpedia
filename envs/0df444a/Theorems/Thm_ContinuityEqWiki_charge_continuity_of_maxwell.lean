-- Prove2me | Theorems.Thm_ContinuityEqWiki_charge_continuity_of_maxwell
-- name    : ContinuityEqWiki.charge_continuity_of_maxwell
-- status  : Open
-- author  : @Lucas
-- created : 2026-10-09T21:28:18.529989+00:00
-- url     : https://prove2.me/theorems/e13f36d0-3194-46b7-a504-606ab17bc75b
-- title:
--   Charge conservation from Maxwell's equations: $\nabla\cdot\mathbf J+\partial_t\rho=0$
-- statement:
--   Let $\mathbf H,\mathbf D,\mathbf J:\mathbb R\times\mathbb R^3\to\mathbb R^3$ and $\rho:\mathbb R\times\mathbb R^3\to\mathbb R$ be time-dependent fields. Assume that $\mathbf H(t,\cdot)$ is $C^2$ for every $t$ and that $\mathbf D$ is $C^2$ jointly in $(t,x)$. Suppose Ampère's law with Maxwell's correction and Gauss's law hold everywhere:
--   $$\nabla\times\mathbf H=\mathbf J+\frac{\partial\mathbf D}{\partial t},\qquad \nabla\cdot\mathbf D=\rho .$$
--   Then the continuity equation for electric charge holds everywhere:
--   $$\nabla\cdot\mathbf J+\frac{\partial\rho}{\partial t}=0 .$$
--
--   This is the statement that charge conservation is an automatic consequence of Maxwell's equations.
-- source:
--   Wikipedia, "Continuity equation", revision oldid=1378634825, https://en.wikipedia.org/w/index.php?title=Continuity_equation&oldid=1378634825, section "Electromagnetism", box "Consistency with Maxwell's equations"

import Mathlib
import Definitions.Def_ContinuityEqWiki_Defs

namespace ContinuityEqWiki

theorem charge_continuity_of_maxwell (H D J : ℝ → Space → Space) (ρ : ℝ → Space → ℝ)
    (hH : ∀ t, ContDiff ℝ 2 (H t)) (hD : ContDiff ℝ 2 (Function.uncurry D))
    (ampere : ∀ t x, curl (H t) x = J t x + timeDeriv D t x)
    (gauss : ∀ t x, div (D t) x = ρ t x) :
    ∀ t x, div (J t) x + timeDeriv ρ t x = 0 := by sorry

end ContinuityEqWiki
