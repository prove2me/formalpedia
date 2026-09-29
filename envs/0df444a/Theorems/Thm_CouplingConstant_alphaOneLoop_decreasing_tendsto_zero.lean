-- Prove2me | Theorems.Thm_CouplingConstant_alphaOneLoop_decreasing_tendsto_zero
-- name    : CouplingConstant.alphaOneLoop_decreasing_tendsto_zero
-- status  : Proved
-- author  : @Lucas
-- created : 2026-09-20T21:14:51.928618+00:00
-- url     : https://prove2.me/theorems/a21ed2b6-feee-4445-b0b8-3be4144165b6
-- title:
--   $\alpha(Q)=1/(\beta_0\log(Q^2/\Lambda^2))$ is strictly decreasing above $\Lambda$ and tends to $0$
-- statement:
--   The qualitative behaviour the source attributes to the strong coupling — it decreases with energy, and does so all the way to zero — read off the explicit one-loop formula.
--
--   Let $\beta_0 > 0$, $\Lambda > 0$ and
--   $$\alpha(Q) \;=\; \frac{1}{\beta_0\,\log\!\big(Q^{2}/\Lambda^{2}\big)} .$$
--   Then both of the following hold.
--
--   1. **Strict decrease above the QCD scale.** For all energies $Q_1, Q_2$ with $\Lambda < Q_1 < Q_2$,
--   $$\alpha(Q_2) \;<\; \alpha(Q_1).$$
--   2. **Vanishing at high energy.** $\alpha(Q) \to 0$ as $Q \to \infty$.
--
--   Together these say that above the QCD scale the coupling is a strictly decreasing function of the probe energy which dies off at infinity; conversely it grows as the energy is lowered towards $\Lambda$, the regime in which the source warns that perturbation theory can no longer be relied upon. Nothing is claimed about $Q \le \Lambda$, where the logarithm is zero or negative.
-- source:
--   Wikipedia, "Coupling constant", https://en.wikipedia.org/w/index.php?title=Coupling_constant&oldid=1354339557 — sections "Beta functions", "QED and the Landau pole", "QCD and asymptotic freedom", "QCD scale"

import Mathlib
import Definitions.Def_CouplingConstantDefs

namespace CouplingConstant
theorem alphaOneLoop_decreasing_tendsto_zero (beta0 Lam : ℝ) (hbeta : 0 < beta0)
    (hLam : 0 < Lam) :
    (∀ Q1 Q2 : ℝ, Lam < Q1 → Q1 < Q2 →
        alphaOneLoop beta0 Lam Q2 < alphaOneLoop beta0 Lam Q1) ∧
      Filter.Tendsto (alphaOneLoop beta0 Lam) Filter.atTop (nhds 0) := by sorry
end CouplingConstant
