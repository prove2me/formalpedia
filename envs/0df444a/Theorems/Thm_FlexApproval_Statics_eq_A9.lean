-- Prove2me | Theorems.Thm_FlexApproval_Statics_eq_A9
-- name    : FlexApproval.Statics.eq_A9
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-20T12:36:34.804814+00:00
-- url     : https://prove2.me/theorems/dc715eb4-6134-4edd-bd1f-c58ca361c994
-- title:
--   Eq. (A.9), p. 33 — closed form of the derivative V′(α) on (0, 1)
-- statement:
--   Under the standing assumptions, for every $0<\alpha<1$ write $\theta=\delta\sqrt{I_n}$ and $g'(\alpha)=e^{\theta\,\Phi^{-1}(1-\alpha)-\theta^2/2}$. Then the power curve $\alpha\mapsto1-\Phi(\Phi^{-1}(1-\alpha)-\theta)$ has derivative $g'(\alpha)$ at $\alpha$, and $V$ is differentiable at $\alpha$ with
--   $$V'(\alpha)=\Big(Q_E\,\frac{K}{(1+\psi_E(\alpha))^2}\,\frac{\tilde\lambda p\,g'(\alpha)}{K\mu_E}-Q_I\cdot1\cdot\frac{\tilde\lambda(1-p)}{\mu_I}\Big)\mathrm{WTP}+C_{AE}\,\tilde\lambda p\,g'(\alpha)-C_{AI}\,\tilde\lambda(1-p)-C_{RE}\big(-\tilde\lambda p\,g'(\alpha)\big).$$
--
--   This is (A.9) of the paper, $V'=(Q_E\,\partial\mathbb E[N_E]/\partial\psi_E\cdot\partial\psi_E/\partial\alpha-Q_I\,\partial\mathbb E[N_I]/\partial\psi_I\cdot\partial\psi_I/\partial\alpha)\mathrm{WTP}+(C_{AE}\,\partial\lambda_{AE}/\partial\alpha-C_{AI}\,\partial\lambda_{AI}/\partial\alpha-C_{RE}\,\partial\lambda_{RE}/\partial\alpha)$, with each partial derivative written out. All sign computations (A.10)–(A.20) differentiate this expression in a parameter.
--
--   **Formalization Note** The factor $g'(\alpha)$ is the exponential printed in (A.19)–(A.20).
-- source:
--   Bravo, Corcoran & Long, Flexible Drug Approval Policies, SSRN working paper 3027263 (version of 17 Jul 2019), p. 33, Eq. (A.9)

import Mathlib
import Definitions.Def_FlexApproval_Statics_Model

namespace FlexApproval.Statics

open Cohen2019.Robust

/-- Eq. (A.9), p. 33: for `0 < α < 1`, the power curve has derivative `gp θ α` and
`V′(α) = (Q_E ∂E[N_E]/∂ψ_E · ∂ψ_E/∂α − Q_I ∂E[N_I]/∂ψ_I · ∂ψ_I/∂α) WTP
  + (C_AE ∂λ_AE/∂α − C_AI ∂λ_AI/∂α − C_RE ∂λ_RE/∂α)`, each factor written out. -/
theorem eq_A9 (P : Params) (hP : P.Standing) (α : ℝ) (hα : α ∈ Set.Ioo (0 : ℝ) 1) :
    HasDerivAt (pw (theta P)) (gp (theta P) α) α ∧
    HasDerivAt (V P)
      ((P.QE * ((P.K : ℝ) / (1 + psiE P α) ^ 2) *
            (lamTilde P * P.p * gp (theta P) α / ((P.K : ℝ) * P.muE)) -
          P.QI * 1 * (lamTilde P * (1 - P.p) / P.muI)) * P.WTP +
        (P.CAE * (lamTilde P * P.p * gp (theta P) α) - P.CAI * (lamTilde P * (1 - P.p)) -
          P.CRE * (-(lamTilde P * P.p * gp (theta P) α)))) α := by sorry

end FlexApproval.Statics
