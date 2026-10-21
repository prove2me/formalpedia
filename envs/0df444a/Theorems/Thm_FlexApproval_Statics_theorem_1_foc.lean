-- Prove2me | Theorems.Thm_FlexApproval_Statics_theorem_1_foc
-- name    : FlexApproval.Statics.theorem_1_foc
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-20T12:36:36.634911+00:00
-- url     : https://prove2.me/theorems/f7dc4701-9eb3-4117-8fde-4b3deb47a969
-- title:
--   Theorem 1 (second part), p. 12 — the optimal significance level is unique, interior, and solves the first-order condition (5)
-- statement:
--   Under the standing assumptions of the drug-approval model, there is exactly one optimal approval policy $\alpha^*\in[0,1]$ (a maximizer of $V$ on $[0,1]$). It lies in the open interval $(0,1)$ and satisfies the first-order condition (5):
--   $$\alpha^*=1-\Phi\left(\frac{1}{\delta\sqrt{I_n}}\log\left(\frac{1-p}{p}\cdot\frac{C_{AI}+\mathrm{WTP}\cdot Q_I/\mu_I}{\mathrm{WTP}\cdot Q_E/\big(\mu_E(1+\psi_E(\alpha^*))^2\big)+C_{RE}+C_{AE}}\right)+\frac{\delta\sqrt{I_n}}{2}\right).$$
--
--   The equation is not a closed form, since $\psi_E(\alpha^*)$ appears on the right; it characterizes $\alpha^*$ implicitly and is the starting point of the comparative statics.
--
--   **Formalization Note** Uniqueness and interiority are the paper's sentence introducing Theorem 1 ("the optimal significance level $\alpha^*$ is unique and is the solution to a non-linear equation"). The standing assumptions $0<p<1$, $Q_E>0$ and $C_{AI}+\mathrm{WTP}\,Q_I/\mu_I>0$ keep the argument of the logarithm positive.
-- source:
--   Bravo, Corcoran & Long, Flexible Drug Approval Policies, SSRN working paper 3027263 (version of 17 Jul 2019), p. 12, Theorem 1 (second part), Eq. (5), and the sentence preceding Theorem 1

import Mathlib
import Definitions.Def_FlexApproval_Statics_Model

namespace FlexApproval.Statics

open Cohen2019.Robust

/-- Theorem 1 (second part), p. 12: the optimal significance level is unique, lies in `(0, 1)`, and
satisfies the first-order condition (5)
`α* = 1 − Φ((1/(δ√I_n)) log(((1 − p)/p) (C_AI + WTP·Q_I/µ_I) /
  (WTP·Q_E/(µ_E(1 + ψ_E(α*))²) + C_RE + C_AE)) + δ√I_n/2)`. -/
theorem theorem_1_foc (P : Params) (hP : P.Standing) :
    (∃! a : ℝ, IsOptimal P a) ∧
    ∀ a : ℝ, IsOptimal P a →
      a ∈ Set.Ioo (0 : ℝ) 1 ∧
      a = 1 - Phi (1 / theta P *
            Real.log ((1 - P.p) / P.p * ((P.CAI + P.WTP * P.QI / P.muI) /
              (P.WTP * P.QE / (P.muE * (1 + psiE P a) ^ 2) + P.CRE + P.CAE))) +
          theta P / 2) := by sorry

end FlexApproval.Statics
