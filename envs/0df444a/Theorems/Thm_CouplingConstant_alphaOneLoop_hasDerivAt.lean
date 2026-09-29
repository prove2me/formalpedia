-- Prove2me | Theorems.Thm_CouplingConstant_alphaOneLoop_hasDerivAt
-- name    : CouplingConstant.alphaOneLoop_hasDerivAt
-- status  : Proved
-- author  : @Lucas
-- created : 2026-09-20T21:14:33.473857+00:00
-- url     : https://prove2.me/theorems/d3a3a509-12bd-49bc-825b-ca26a6a96ade
-- title:
--   The one-loop QCD coupling solves $d\alpha/dQ=-(2/Q)\beta_0\alpha^2$
-- statement:
--   The closed formula quoted in the source for the strong coupling is indeed a solution of the one-loop renormalization-group equation for $\alpha$.
--
--   Let $\beta_0 > 0$ and $\Lambda > 0$, and let
--   $$\alpha(Q) \;=\; \frac{1}{\beta_0\,\log\!\big(Q^{2}/\Lambda^{2}\big)} .$$
--   Then for every energy $Q > \Lambda$ the function $\alpha$ is differentiable at $Q$ with
--   $$\frac{d\alpha}{dQ}(Q) \;=\; -\frac{2}{Q}\,\beta_0\,\alpha(Q)^{2},$$
--   which is the statement $d\alpha/d\log(Q^{2}) = -\beta_0\,\alpha^{2}$ written in the variable $Q$.
--
--   The hypothesis $Q > \Lambda$ keeps $\log(Q^2/\Lambda^2)$ strictly positive, so the formula is well defined and the sign of the derivative is unambiguous: $\alpha$ decreases as the energy grows.
-- source:
--   Wikipedia, "Coupling constant", https://en.wikipedia.org/w/index.php?title=Coupling_constant&oldid=1354339557 — sections "Beta functions", "QED and the Landau pole", "QCD and asymptotic freedom", "QCD scale"

import Mathlib
import Definitions.Def_CouplingConstantDefs

namespace CouplingConstant
theorem alphaOneLoop_hasDerivAt (beta0 Lam Q : ℝ) (hbeta : 0 < beta0) (hLam : 0 < Lam)
    (hQ : Lam < Q) :
    HasDerivAt (alphaOneLoop beta0 Lam)
      (-(2 / Q) * beta0 * (alphaOneLoop beta0 Lam Q) ^ 2) Q := by sorry
end CouplingConstant
