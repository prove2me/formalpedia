-- Prove2me | Theorems.Thm_CouplingConstantRG_landau_pole_mu
-- name    : CouplingConstantRG.landau_pole_mu
-- status  : Proved
-- author  : @Lucas
-- created : 2026-10-03T15:49:13.586377+00:00
-- url     : https://prove2.me/theorems/751c9ef5-39d7-4797-b5c1-27888520a45d
-- title:
--   Landau pole: no one-loop solution reaches the pole scale when $b>0$
-- statement:
--   "The perturbative beta function tells us that the coupling continues to increase, and QED becomes strongly coupled at high energy. In fact the coupling apparently becomes infinite at some finite energy. This phenomenon ... is called the Landau pole."
--
--   Let $b > 0$ be a one-loop coefficient of the QED sign, $\mu_0 > 0$ a reference energy and $\alpha_0 > 0$ the coupling there. Then there is **no** function $\alpha$ with $\alpha(\mu_0) = \alpha_0$ satisfying
--   $$\mu\,\frac{d\alpha}{d\mu}(\mu) \;=\; b\,\alpha(\mu)^2$$
--   at every energy of the closed interval
--   $$\Big[\mu_0,\; \mu_0\,e^{1/(b\alpha_0)}\Big].$$
--
--   The upper endpoint is the pole scale predicted by the one-loop equation itself, namely the energy at which the inverse coupling $1/\alpha_0 - b\ln(\mu/\mu_0)$ reaches zero. Stating the pole as non-existence of a solution, rather than as a divergence of one chosen formula, is what makes it an obstruction: no candidate running coupling of any kind survives to that energy.
-- source:
--   Wikipedia, "Coupling constant", https://en.wikipedia.org/w/index.php?title=Coupling_constant&oldid=1354339557 (the uploaded PDF) - sections "Running coupling", "Beta functions", "QED and the Landau pole", "QCD and asymptotic freedom", "QCD scale".

import Mathlib
import Definitions.Def_CouplingConstantRGDefs

namespace CouplingConstantRG

theorem landau_pole_mu (b μ₀ α₀ : ℝ) (hb : 0 < b) (hμ₀ : 0 < μ₀) (hα₀ : 0 < α₀) :
    ¬ ∃ α : ℝ → ℝ, α μ₀ = α₀ ∧
      IsMuRunning b α (Set.Icc μ₀ (μ₀ * Real.exp (1 / (b * α₀)))) := by sorry

end CouplingConstantRG
