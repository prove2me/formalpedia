-- Prove2me | Theorems.Thm_CouplingConstantRG_betaFunctionMu_neg_strictAntiOn
-- name    : CouplingConstantRG.betaFunctionMu_neg_strictAntiOn
-- status  : Proved
-- author  : @Lucas
-- created : 2026-10-03T14:40:18.888172+00:00
-- url     : https://prove2.me/theorems/f29513c1-8850-49ec-b24e-8ad5becdcec4
-- title:
--   Negative beta function: the coupling decreases with energy
-- statement:
--   "In non-abelian gauge theories, the beta function can be negative ... and as a result the QCD coupling decreases at high energies." This milestone is the implication behind that "as a result".
--
--   Let $g$ be differentiable at every positive energy scale and suppose its beta function is strictly negative there,
--   $$\mu\,\frac{d g}{d\mu}(\mu) \;<\; 0 \qquad\text{for all } \mu > 0 .$$
--   Then $g$ is strictly decreasing on $(0, \infty)$: if $0 < \mu_1 < \mu_2$ then $g(\mu_2) < g(\mu_1)$.
--
--   It is the mirror image of the positive-sign statement, and the general form of the behaviour that the explicit one-loop QCD coupling exhibits; it says nothing yet about the rate of the decrease or about a limit at infinity.
-- source:
--   Wikipedia, "Coupling constant", https://en.wikipedia.org/w/index.php?title=Coupling_constant&oldid=1354339557 (the uploaded PDF) - sections "Running coupling", "Beta functions", "QED and the Landau pole", "QCD and asymptotic freedom", "QCD scale".

import Mathlib
import Definitions.Def_CouplingConstantRGDefs

namespace CouplingConstantRG

theorem betaFunctionMu_neg_strictAntiOn (g : ℝ → ℝ)
    (hg : ∀ μ, 0 < μ → DifferentiableAt ℝ g μ)
    (hβ : ∀ μ, 0 < μ → betaFunctionMu g μ < 0) :
    StrictAntiOn g (Set.Ioi 0) := by sorry

end CouplingConstantRG
