-- Prove2me | Theorems.Thm_CouplingConstantRG_alphaOneLoop_isMuRunning
-- name    : CouplingConstantRG.alphaOneLoop_isMuRunning
-- status  : Proved
-- author  : @Lucas
-- created : 2026-10-03T14:59:44.552177+00:00
-- url     : https://prove2.me/theorems/2ddad8f3-0f1e-4b11-9860-a32827d17e3c
-- title:
--   The quoted $\alpha_s(k^2)$ solves the one-loop equation $\mu\,d\alpha/d\mu = -2\beta_0\alpha^2$
-- statement:
--   The source quotes the one-loop strong coupling as a formula,
--   $$\alpha_s(k^2) \;\approx\; \frac{1}{\beta_0 \ln(k^2/\Lambda^2)},$$
--   and separately describes the running of a coupling by a differential equation. This milestone connects the two: the quoted formula is an exact solution of the one-loop renormalization-group equation in the energy scale.
--
--   Let $\beta_0 > 0$ be the one-loop coefficient and $\Lambda > 0$ the QCD scale, and let $\alpha(Q) = 1/(\beta_0 \ln(Q^2/\Lambda^2))$. Then at every energy $Q > \Lambda$,
--   $$Q\,\frac{d\alpha}{dQ}(Q) \;=\; -2\beta_0\,\alpha(Q)^2 .$$
--
--   The coefficient $-2\beta_0$ is negative, so the explicit QCD formula falls into the asymptotically free branch of the mission's goal theorem, and the factor $2$ records that the source's formula is written in $k^2$ while the equation here is written in the energy $Q$ itself.
-- source:
--   Wikipedia, "Coupling constant", https://en.wikipedia.org/w/index.php?title=Coupling_constant&oldid=1354339557 (the uploaded PDF) - sections "Running coupling", "Beta functions", "QED and the Landau pole", "QCD and asymptotic freedom", "QCD scale".

import Mathlib
import Definitions.Def_CouplingConstantDefs
import Definitions.Def_CouplingConstantRGDefs

namespace CouplingConstantRG

theorem alphaOneLoop_isMuRunning (β₀ Λ : ℝ) (hβ₀ : 0 < β₀) (hΛ : 0 < Λ) :
    IsMuRunning (-2 * β₀) (CouplingConstant.alphaOneLoop β₀ Λ) (Set.Ioi Λ) := by sorry

end CouplingConstantRG
