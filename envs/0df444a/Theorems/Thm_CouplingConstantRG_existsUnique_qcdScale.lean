-- Prove2me | Theorems.Thm_CouplingConstantRG_existsUnique_qcdScale
-- name    : CouplingConstantRG.existsUnique_qcdScale
-- status  : Proved
-- author  : @Lucas
-- created : 2026-10-03T15:25:17.161943+00:00
-- url     : https://prove2.me/theorems/e152d7f9-9e27-45e6-aa41-b85733069fc6
-- title:
--   The QCD scale $\Lambda$ is determined by the coupling at one energy
-- statement:
--   The source stresses that "the actual value of the coupling constant is only defined at a given energy scale", quotes $\alpha_s(M_Z^2) = 0.1179 \pm 0.0010$ at the $Z$ mass, and treats $\Lambda$ — the QCD scale — as the parameter carrying that information. This milestone is the statement that the two descriptions are equivalent: one measurement fixes $\Lambda$, and fixes it uniquely.
--
--   Let $\beta_0 > 0$ be the one-loop coefficient, $\mu_0 > 0$ a reference energy, and $\alpha_0 > 0$ the value of the strong coupling measured there. Then there is exactly one scale $\Lambda$ with
--   $$0 < \Lambda < \mu_0 \qquad\text{and}\qquad \frac{1}{\beta_0 \ln(\mu_0^2/\Lambda^2)} \;=\; \alpha_0 .$$
--
--   This is the dimensional-transmutation step: a dimensionless measured number at a given energy is traded for a dimensionful scale, below the measurement energy, which then determines the coupling at every energy above it.
-- source:
--   Wikipedia, "Coupling constant", https://en.wikipedia.org/w/index.php?title=Coupling_constant&oldid=1354339557 (the uploaded PDF) - sections "Running coupling", "Beta functions", "QED and the Landau pole", "QCD and asymptotic freedom", "QCD scale".

import Mathlib
import Definitions.Def_CouplingConstantDefs
import Definitions.Def_CouplingConstantRGDefs

namespace CouplingConstantRG

theorem existsUnique_qcdScale (β₀ μ₀ α₀ : ℝ) (hβ₀ : 0 < β₀) (hμ₀ : 0 < μ₀)
    (hα₀ : 0 < α₀) :
    ∃! Λ : ℝ, 0 < Λ ∧ Λ < μ₀ ∧ CouplingConstant.alphaOneLoop β₀ Λ μ₀ = α₀ := by sorry

end CouplingConstantRG
