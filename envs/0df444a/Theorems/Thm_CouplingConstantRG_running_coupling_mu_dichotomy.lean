-- Prove2me | Theorems.Thm_CouplingConstantRG_running_coupling_mu_dichotomy
-- name    : CouplingConstantRG.running_coupling_mu_dichotomy
-- status  : Proved
-- author  : @Lucas
-- created : 2026-10-03T16:26:52.965064+00:00
-- url     : https://prove2.me/theorems/d71e2900-7bc3-40dd-8e59-27082503f369
-- title:
--   Goal: the one-loop running dichotomy in the energy scale
-- statement:
--   The goal of the mission: the sign of the one-loop coefficient decides, completely, how a coupling runs above a reference energy.
--
--   Fix a reference energy $\mu_0 > 0$ and a positive coupling value $\alpha_0$ measured there, and consider the one-loop equation in the energy scale,
--   $$\mu\,\frac{d\alpha}{d\mu}(\mu) \;=\; b\,\alpha(\mu)^2 .$$
--
--   1. **Asymptotically free branch ($b < 0$).** Every coupling $\alpha$ with $\alpha(\mu_0) = \alpha_0$ satisfying the equation at all energies $\mu \ge \mu_0$ is given in closed form by
--   $$\alpha(\mu) \;=\; \frac{\alpha_0}{1 - b\,\alpha_0 \ln(\mu/\mu_0)}, \qquad \mu \ge \mu_0,$$
--   and tends to $0$ as $\mu \to \infty$. This is asymptotic freedom, with the solution unique rather than merely exhibited.
--
--   2. **Landau-pole branch ($b > 0$).** No coupling with $\alpha(\mu_0) = \alpha_0$ satisfies the equation on the entire closed interval $[\mu_0,\ \mu_0 e^{1/(b\alpha_0)}]$, whose upper endpoint is the pole scale the equation itself predicts.
--
--   The two branches are the mathematical content of the source's QED and QCD sections, in the variable in which the source defines the beta function. The case $b = 0$ is outside the statement; it is covered by the scale-invariance milestone.
-- source:
--   Wikipedia, "Coupling constant", https://en.wikipedia.org/w/index.php?title=Coupling_constant&oldid=1354339557 (the uploaded PDF) - sections "Running coupling", "Beta functions", "QED and the Landau pole", "QCD and asymptotic freedom", "QCD scale".

import Mathlib
import Definitions.Def_CouplingConstantRGDefs

namespace CouplingConstantRG

theorem running_coupling_mu_dichotomy (b μ₀ α₀ : ℝ) (hμ₀ : 0 < μ₀) (hα₀ : 0 < α₀) :
    (b < 0 → ∀ α : ℝ → ℝ, α μ₀ = α₀ → IsMuRunning b α (Set.Ici μ₀) →
        (∀ μ, μ₀ ≤ μ → α μ = α₀ / (1 - b * α₀ * Real.log (μ / μ₀))) ∧
          Filter.Tendsto α Filter.atTop (nhds 0)) ∧
      (0 < b → ¬ ∃ α : ℝ → ℝ, α μ₀ = α₀ ∧
        IsMuRunning b α (Set.Icc μ₀ (μ₀ * Real.exp (1 / (b * α₀))))) := by sorry

end CouplingConstantRG
