-- Prove2me | Theorems.Thm_EquilibriumExperiment_Gradient_proposition_12
-- name    : EquilibriumExperiment.Gradient.proposition_12
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-22T12:39:35.186995+00:00
-- url     : https://prove2.me/theorems/98726ae8-7c3c-4353-a1af-4cd5e5839902
-- title:
--   Proposition 12 (second equality), p. 37 — closed form of the mean-field utility gradient u′_a(p)
-- statement:
--   Under the standing assumptions, fix a payment $p > 0$ with $\mathbb E[f_B(p\,\bar\omega)] > 0$, write $\mu = \mu(p)$ for the mean-field supply and $\mu'(p)$ for the right-hand side of (3.20). Then the mean-field platform utility $u(p) = (r(d/\mu(p)) - p\,\omega(d/\mu(p)))\,\mu(p)$ of (3.15) is differentiable at $p$, with
--   $$u'(p) = \mu'(p)\Bigl[r\Bigl(\frac d\mu\Bigr) - p\,\omega\Bigl(\frac d\mu\Bigr) - \Bigl(r'\Bigl(\frac d\mu\Bigr) - p\,\omega'\Bigl(\frac d\mu\Bigr)\Bigr)\frac d\mu\Bigr] - \omega\Bigl(\frac d\mu\Bigr)\mu.$$
--
--   This is the target quantity of the goal theorem: the estimator $\hat\Gamma$ of (4.3) is the plug-in version of this formula.
--
--   **Formalization Note** Only the second equality of Proposition 12 is formalized; the first concerns the pre-limit utility $u^{(n)}$, which is not modelled. $\mu'(p)$ enters through the closed form (3.20), and Lemma 4 is the statement that it is the derivative of $\mu(\cdot)$. $r'$ and $\omega'$ are Lean's `deriv`; both functions are smooth on $(0,\infty)$ and $d/\mu > 0$. The positivity condition makes $\mu(p)$ exist (see Lemma 2).
-- source:
--   Wager & Xu, Experimenting in Equilibrium, arXiv:1903.02124v5, p. 37, Proposition 12 (statement continues on p. 38), second equality; u_a from (3.15), p. 18

import Mathlib
import Definitions.Def_EquilibriumExperiment_Gradient_Model

open MeasureTheory ProbabilityTheory Filter Topology

namespace EquilibriumExperiment.Gradient

theorem proposition_12 {B : Type} [MeasurableSpace B] (M : Market B) (hM : M.Standing)
    {p : ℝ} (hp : 0 < p) (hpos : 0 < ∫ b, M.f b (p * M.omegaSup) ∂M.β) :
    HasDerivAt M.u
      (M.muLimDeriv p *
          (M.r (M.d / M.muLim p) - p * M.ω (M.d / M.muLim p) -
            (deriv M.r (M.d / M.muLim p) - p * deriv M.ω (M.d / M.muLim p)) *
              (M.d / M.muLim p)) -
        M.ω (M.d / M.muLim p) * M.muLim p) p := by sorry

end EquilibriumExperiment.Gradient
