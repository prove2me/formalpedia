-- Prove2me | Theorems.Thm_FlexApproval_Statics_eq_A10_A15
-- name    : FlexApproval.Statics.eq_A10_A15
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-20T12:36:44.563773+00:00
-- url     : https://prove2.me/theorems/2ea690a0-85fa-479b-bc43-5e55fc496e12
-- title:
--   Eqs. (A.10)–(A.15), p. 33 — ∂V′/∂x ≥ 0 for x = Q_E, C_AE, C_RE, µ_I and ≤ 0 for x = Q_I, C_AI
-- statement:
--   Under the standing assumptions, fix $0<\alpha<1$ and write $g'(\alpha)=e^{\delta\sqrt{I_n}\,\Phi^{-1}(1-\alpha)-\delta^2I_n/2}$. Varying one parameter at a time and keeping the others fixed, the derivative of $V'(\alpha)$ with respect to that parameter is:
--
--   1. (A.10) $Q_E$: $\ \mathrm{WTP}\cdot\dfrac{K}{(1+\psi_E(\alpha))^2}\cdot\dfrac{\tilde\lambda p\,g'(\alpha)}{K\mu_E}\ \ge0$;
--   2. (A.11) $Q_I$: $\ \mathrm{WTP}\cdot\Big(-1\cdot\dfrac{\tilde\lambda(1-p)}{\mu_I}\Big)\le0$;
--   3. (A.12) $C_{AE}$: $\ \partial\lambda_{AE}/\partial\alpha=\tilde\lambda p\,g'(\alpha)\ge0$;
--   4. (A.13) $C_{AI}$: $\ -\partial\lambda_{AI}/\partial\alpha=-\tilde\lambda(1-p)\le0$;
--   5. (A.14) $C_{RE}$: $\ -\partial\lambda_{RE}/\partial\alpha=\tilde\lambda p\,g'(\alpha)\ge0$;
--   6. (A.15) $\mu_I$: $\ \mathrm{WTP}\cdot\Big(-Q_I\,\dfrac{\partial^2\psi_I}{\partial\alpha\,\partial\mu_I}\Big)=\mathrm{WTP}\cdot Q_I\,\dfrac{\tilde\lambda(1-p)}{\mu_I^2}\ge0$.
--
--   By (A.8) these signs are the signs of $\partial\alpha^*/\partial x$, giving the parts of Proposition 1 for these six parameters.
--
--   **Formalization Note** The paper states the signs at $\alpha=\alpha^*$; the statement gives them at every $0<\alpha<1$, which includes $\alpha^*$. The paper's sign expressions omit the positive factor $\mathrm{WTP}$ where it multiplies; the derivatives here include it.
-- source:
--   Bravo, Corcoran & Long, Flexible Drug Approval Policies, SSRN working paper 3027263 (version of 17 Jul 2019), p. 33, proof of Proposition 1, Eqs. (A.10)–(A.15)

import Mathlib
import Definitions.Def_FlexApproval_Statics_Model

namespace FlexApproval.Statics

open Cohen2019.Robust

/-- Eqs. (A.10)–(A.15), p. 33: at every `0 < α < 1`, the partial derivative of `V′(α)` with respect
to `Q_E`, `C_AE`, `C_RE`, `µ_I` is `≥ 0` and with respect to `Q_I`, `C_AI` is `≤ 0`; each is given in
closed form. -/
theorem eq_A10_A15 (P : Params) (hP : P.Standing) (α : ℝ) (hα : α ∈ Set.Ioo (0 : ℝ) 1) :
    -- (A.10) Q_E
    (HasDerivAt (fun x => deriv (V { P with QE := x }) α)
        (P.WTP * (((P.K : ℝ) / (1 + psiE P α) ^ 2) *
          (lamTilde P * P.p * gp (theta P) α / ((P.K : ℝ) * P.muE)))) P.QE ∧
      0 ≤ P.WTP * (((P.K : ℝ) / (1 + psiE P α) ^ 2) *
          (lamTilde P * P.p * gp (theta P) α / ((P.K : ℝ) * P.muE)))) ∧
    -- (A.11) Q_I
    (HasDerivAt (fun x => deriv (V { P with QI := x }) α)
        (P.WTP * (-(1 * (lamTilde P * (1 - P.p) / P.muI)))) P.QI ∧
      P.WTP * (-(1 * (lamTilde P * (1 - P.p) / P.muI))) ≤ 0) ∧
    -- (A.12) C_AE
    (HasDerivAt (fun x => deriv (V { P with CAE := x }) α)
        (lamTilde P * P.p * gp (theta P) α) P.CAE ∧
      0 ≤ lamTilde P * P.p * gp (theta P) α) ∧
    -- (A.13) C_AI
    (HasDerivAt (fun x => deriv (V { P with CAI := x }) α)
        (-(lamTilde P * (1 - P.p))) P.CAI ∧
      -(lamTilde P * (1 - P.p)) ≤ 0) ∧
    -- (A.14) C_RE
    (HasDerivAt (fun x => deriv (V { P with CRE := x }) α)
        (-(-(lamTilde P * P.p * gp (theta P) α))) P.CRE ∧
      0 ≤ -(-(lamTilde P * P.p * gp (theta P) α))) ∧
    -- (A.15) µ_I
    (HasDerivAt (fun x => deriv (V { P with muI := x }) α)
        (P.WTP * (-P.QI * (-(lamTilde P * (1 - P.p)) / P.muI ^ 2))) P.muI ∧
      0 ≤ P.WTP * (-P.QI * (-(lamTilde P * (1 - P.p)) / P.muI ^ 2))) := by sorry

end FlexApproval.Statics
