-- Prove2me | Theorems.Thm_FlexApproval_Statics_eq_A20
-- name    : FlexApproval.Statics.eq_A20
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-20T12:36:56.634637+00:00
-- url     : https://prove2.me/theorems/76e17db0-9ff4-40b2-afbc-8883a9ee9bcb
-- title:
--   Eq. (A.20), p. 34 — ∂V′(α)/∂p in closed form, positive when ψ_E(α) < 1
-- statement:
--   Under the standing assumptions, for every $0<\alpha<1$, varying the prior probability $p$ of effectiveness with the other parameters fixed, $V'(\alpha)$ is differentiable in $p$ with
--   $$\frac{\partial V'(\alpha)}{\partial p}=\tilde\lambda\,e^{\Phi^{-1}(1-\alpha)\delta\sqrt{I_n}-\delta^2I_n/2}\left(\frac{\mathrm{WTP}\cdot Q_E\,(1-\psi_E(\alpha))}{\mu_E(1+\psi_E(\alpha))^3}+C_{AE}+C_{RE}\right)+\mathrm{WTP}\cdot Q_I\,\frac{\tilde\lambda}{\mu_I}+C_{AI}\tilde\lambda,$$
--   and this is $>0$ whenever $\psi_E(\alpha)<1$.
--
--   By (A.8), $\psi_E(\alpha^*)<1$ makes $\alpha^*$ nondecreasing in $p$ (Proposition 1(c)).
--
--   **Formalization Note** The printed (A.20) writes $\mathrm{WTP}\cdot Q_E(1-\psi_E(\alpha^*))$ without the factor $1/(\mu_E(1+\psi_E(\alpha^*))^3)$ that differentiation produces; the factor is positive, so the sign conclusion is unaffected, and the statement gives the correct derivative.
-- source:
--   Bravo, Corcoran & Long, Flexible Drug Approval Policies, SSRN working paper 3027263 (version of 17 Jul 2019), p. 34, proof of Proposition 1, Eq. (A.20)

import Mathlib
import Definitions.Def_FlexApproval_Statics_Model

namespace FlexApproval.Statics

open Cohen2019.Robust

/-- Eq. (A.20), p. 34: at every `0 < α < 1`,
`∂V′(α)/∂p = λ̃ gp(α) (WTP·Q_E (1 − ψ_E(α))/(µ_E(1 + ψ_E(α))³) + C_AE + C_RE) + WTP·Q_I λ̃/µ_I + C_AI λ̃`,
which is `> 0` when `ψ_E(α) < 1`. -/
theorem eq_A20 (P : Params) (hP : P.Standing) (α : ℝ) (hα : α ∈ Set.Ioo (0 : ℝ) 1) :
    HasDerivAt (fun x => deriv (V { P with p := x }) α)
      (lamTilde P * gp (theta P) α *
          (P.WTP * P.QE * (1 - psiE P α) / (P.muE * (1 + psiE P α) ^ 3) + P.CAE + P.CRE) +
        P.WTP * P.QI * lamTilde P / P.muI + P.CAI * lamTilde P) P.p ∧
    (psiE P α < 1 →
      0 < lamTilde P * gp (theta P) α *
          (P.WTP * P.QE * (1 - psiE P α) / (P.muE * (1 + psiE P α) ^ 3) + P.CAE + P.CRE) +
        P.WTP * P.QI * lamTilde P / P.muI + P.CAI * lamTilde P) := by sorry

end FlexApproval.Statics
