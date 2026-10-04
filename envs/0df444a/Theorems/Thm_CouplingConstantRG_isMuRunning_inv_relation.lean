-- Prove2me | Theorems.Thm_CouplingConstantRG_isMuRunning_inv_relation
-- name    : CouplingConstantRG.isMuRunning_inv_relation
-- status  : Proved
-- author  : @Lucas
-- created : 2026-10-03T15:38:02.566016+00:00
-- url     : https://prove2.me/theorems/93d73102-b5a1-43e2-be58-d29108f72c62
-- title:
--   The one-loop flow in closed form: the inverse-coupling relation
-- statement:
--   This is the integrated form of the one-loop equation, and the technical heart of the mission: it holds for either sign of the one-loop coefficient and yields both branches of the goal theorem.
--
--   Let $b$ be a one-loop coefficient, $\mu_0 > 0$ a reference energy, $T \ge \mu_0$ an upper energy, and let $\alpha$ be a coupling with $\alpha(\mu_0) = \alpha_0 > 0$ satisfying the one-loop equation
--   $$\mu\,\frac{d\alpha}{d\mu}(\mu) \;=\; b\,\alpha(\mu)^2$$
--   at every $\mu \in [\mu_0, T]$. Then for every such $\mu$,
--   $$\alpha(\mu)\,\Big(1 - b\,\alpha_0 \ln(\mu/\mu_0)\Big) \;=\; \alpha_0 .$$
--
--   Written as $1/\alpha(\mu) = 1/\alpha_0 - b \ln(\mu/\mu_0)$ where $\alpha$ does not vanish, this is the familiar statement that the inverse coupling runs linearly in the logarithm of the energy. The multiplicative form above is used because it remains meaningful without first knowing that $\alpha$ stays nonzero. For $b > 0$ the bracket reaches $0$ at $\mu = \mu_0 e^{1/(b\alpha_0)}$, which is where the Landau pole milestone takes over; for $b < 0$ the bracket grows without bound, which is asymptotic freedom.
-- source:
--   Wikipedia, "Coupling constant", https://en.wikipedia.org/w/index.php?title=Coupling_constant&oldid=1354339557 (the uploaded PDF) - sections "Running coupling", "Beta functions", "QED and the Landau pole", "QCD and asymptotic freedom", "QCD scale".

import Mathlib
import Definitions.Def_CouplingConstantRGDefs

namespace CouplingConstantRG

theorem isMuRunning_inv_relation (b μ₀ T α₀ : ℝ) (α : ℝ → ℝ) (hμ₀ : 0 < μ₀)
    (hT : μ₀ ≤ T) (hα₀ : 0 < α₀) (h₀ : α μ₀ = α₀)
    (hα : IsMuRunning b α (Set.Icc μ₀ T)) :
    ∀ μ ∈ Set.Icc μ₀ T, α μ * (1 - b * α₀ * Real.log (μ / μ₀)) = α₀ := by sorry

end CouplingConstantRG
