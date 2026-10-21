-- Prove2me | Theorems.Thm_FlexApproval_Statics_eq_A19
-- name    : FlexApproval.Statics.eq_A19
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-20T12:36:56.82828+00:00
-- url     : https://prove2.me/theorems/9eab9ef1-b867-4108-87d3-9a299ae5f9ba
-- title:
--   Eq. (A.19), p. 33 — ∂V′(α)/∂µ_E = −WTP·Q_E·(λ̃/µ_E²)·p·g′(α)·(1 − ψ_E)/(1 + ψ_E)³, ≤ 0 when ψ_E(α) < 1
-- statement:
--   Under the standing assumptions, for every $0<\alpha<1$, varying the market exit rate $\mu_E$ of effective drugs with the other parameters fixed, $V'(\alpha)$ is differentiable in $\mu_E$ with
--   $$\frac{\partial V'(\alpha)}{\partial\mu_E}=-\mathrm{WTP}\cdot Q_E\,\frac{\tilde\lambda}{\mu_E^2}\,p\,e^{\Phi^{-1}(1-\alpha)\delta\sqrt{I_n}-\delta^2I_n/2}\,\frac{1-\psi_E(\alpha)}{(1+\psi_E(\alpha))^3},$$
--   and this is $\le0$ whenever $\psi_E(\alpha)<1$.
--
--   By (A.8), $\psi_E(\alpha^*)<1$ makes $\alpha^*$ nonincreasing in $\mu_E$ (Proposition 1(c)).
--
--   **Formalization Note** The printed (A.19) omits the positive factor $\mathrm{WTP}\cdot Q_E$, which does not change the sign; the statement gives the full derivative.
-- source:
--   Bravo, Corcoran & Long, Flexible Drug Approval Policies, SSRN working paper 3027263 (version of 17 Jul 2019), p. 33, proof of Proposition 1, Eq. (A.19)

import Mathlib
import Definitions.Def_FlexApproval_Statics_Model

namespace FlexApproval.Statics

open Cohen2019.Robust

/-- Eq. (A.19), p. 33: at every `0 < α < 1`,
`∂V′(α)/∂µ_E = −WTP·Q_E (λ̃/µ_E²) p gp(α) (1 − ψ_E(α))/(1 + ψ_E(α))³`, which is `≤ 0` when `ψ_E(α) < 1`. -/
theorem eq_A19 (P : Params) (hP : P.Standing) (α : ℝ) (hα : α ∈ Set.Ioo (0 : ℝ) 1) :
    HasDerivAt (fun x => deriv (V { P with muE := x }) α)
      (-(P.WTP * P.QE) * (lamTilde P / P.muE ^ 2) * P.p * gp (theta P) α *
        ((1 - psiE P α) / (1 + psiE P α) ^ 3)) P.muE ∧
    (psiE P α < 1 →
      -(P.WTP * P.QE) * (lamTilde P / P.muE ^ 2) * P.p * gp (theta P) α *
        ((1 - psiE P α) / (1 + psiE P α) ^ 3) ≤ 0) := by sorry

end FlexApproval.Statics
