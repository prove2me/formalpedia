-- Prove2me | Theorems.Thm_AKR2008_osc_continuity_general_solution
-- name    : AKR2008.osc_continuity_general_solution
-- status  : Open
-- author  : @Lucas
-- created : 2026-09-27T23:58:22.579086+00:00
-- url     : https://prove2.me/theorems/c8ada1bd-4214-4ae7-ad92-096ba002dd2b
-- title:
--   Appendix A: the general solution $P=\frac{1}{\cos(\omega t)}f\bigl(\frac{x}{\cos(\omega t)}\bigr)$ of the continuity equation
-- statement:
--   Let $\omega>0$ and $S_{\mathrm{osc}}(x,t)=-\frac{\omega x^2}{2}\tan(\omega t)$. Let $P(x,t)$ be a continuously differentiable function on $\mathbb R^2$. Then $P$ satisfies the continuity equation
--   $$\dot P + \frac{\partial}{\partial x}\Bigl(P\,\frac{\partial S_{\mathrm{osc}}}{\partial x}\Bigr) = 0$$
--   for all $x$ and all $|t|<\pi/(2\omega)$ if and only if there is a function $f:\mathbb R\to\mathbb R$ with
--   $$P(x,t) = \frac{1}{\cos(\omega t)}\,f\Bigl(\frac{x}{\cos(\omega t)}\Bigr)\qquad\text{for all }x\text{ and all }|t|<\frac{\pi}{2\omega}.$$
--
--   This is the paper's claim that, given $S_{\mathrm{osc}}$, the displayed family is *the most general* solution of the continuity equation (the Gaussian $P_{\mathrm{osc}}$ being one member).
--
--   **Formalization Note** The claim is stated on the strip $|\omega t|<\pi/2$ around $t=0$, on which $\cos(\omega t)>0$; $P$ is assumed $C^1$ on all of $\mathbb R^2$ (a regularity convention the paper leaves implicit).
-- source:
--   M. Albers, C. Kiefer, M. Reginatto, Measurement analysis and quantum gravity, Phys. Rev. D 78, 064051 (2008), https://doi.org/10.1103/PhysRevD.78.064051, p. 064051-14, Appendix A

import Mathlib
import Definitions.Def_AKR2008_HybridDefs

namespace AKR2008

theorem osc_continuity_general_solution (ω : ℝ) (hω : 0 < ω) (P : ℝ → ℝ → ℝ)
    (hP : ContDiff ℝ 1 (Function.uncurry P)) :
    (∀ x t, |t| < Real.pi / (2 * ω) →
      deriv (fun s => P x s) t + deriv (fun y => P y t * deriv (fun z => oscS ω z t) y) x = 0) ↔
    ∃ f : ℝ → ℝ, ∀ x t, |t| < Real.pi / (2 * ω) →
      P x t = f (x / Real.cos (ω * t)) / Real.cos (ω * t) := by sorry

end AKR2008
