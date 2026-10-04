-- Prove2me | Theorems.Thm_CouplingConstantRG_betaFunctionMu_eq_deriv_log
-- name    : CouplingConstantRG.betaFunctionMu_eq_deriv_log
-- status  : Proved
-- author  : @Lucas
-- created : 2026-10-03T14:04:31.826364+00:00
-- url     : https://prove2.me/theorems/39f32b40-6ffc-4638-9a3f-95b98bd3f05c
-- title:
--   $\mu\,\partial g/\partial\mu = \partial g/\partial \ln\mu$
-- statement:
--   The source defines the beta function by
--   $$\beta(g) \;=\; \mu\,\frac{\partial g}{\partial \mu} \;=\; \frac{\partial g}{\partial \ln \mu},$$
--   asserting in one line that two different derivatives agree. This milestone is that identity.
--
--   Let $g$ be a coupling regarded as a function of the energy scale, let $\mu > 0$ be a scale at which $g$ is differentiable, and let $\tilde g(t) = g(e^{t})$ be the same coupling regarded as a function of $t = \ln \mu$. Then
--   $$\mu\,\frac{d g}{d \mu}(\mu) \;=\; \frac{d \tilde g}{d t}(\ln \mu).$$
--
--   The identity is what lets the two conventional forms of the renormalization-group equation — in the scale and in its logarithm — be used interchangeably, and it is the bridge between the statements of this mission and formalizations written in the logarithmic variable.
-- source:
--   Wikipedia, "Coupling constant", https://en.wikipedia.org/w/index.php?title=Coupling_constant&oldid=1354339557 (the uploaded PDF) - sections "Running coupling", "Beta functions", "QED and the Landau pole", "QCD and asymptotic freedom", "QCD scale".

import Mathlib
import Definitions.Def_CouplingConstantRGDefs

namespace CouplingConstantRG

theorem betaFunctionMu_eq_deriv_log (g : ℝ → ℝ) (μ : ℝ) (hμ : 0 < μ)
    (hg : DifferentiableAt ℝ g μ) :
    betaFunctionMu g μ = deriv (fun t : ℝ => g (Real.exp t)) (Real.log μ) := by sorry

end CouplingConstantRG
