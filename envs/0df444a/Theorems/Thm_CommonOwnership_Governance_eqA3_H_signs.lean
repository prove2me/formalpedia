-- Prove2me | Theorems.Thm_CommonOwnership_Governance_eqA3_H_signs
-- name    : CommonOwnership.Governance.eqA3_H_signs
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-14T03:08:56.760874+00:00
-- url     : https://prove2.me/theorems/f79e8135-5770-485b-b450-fa6b6250f67d
-- title:
--   Proof of Proposition 3, p. 39 (PDF p. 42) — ∂H/∂ξ < 0 and ∂H/∂γ > 0
-- statement:
--   Let $\beta>0$, $0<\xi<1$, $\gamma>0$, and let $g>0$. For the function of (A3),
--   $$H(\xi,\gamma)=-s+\Big[\gamma\beta\frac{1-\xi}{\xi^2}+\tfrac12(\beta^2-s^2)\Big]g,$$
--   we have
--   $$\frac{\partial H}{\partial\xi}<0,\qquad\frac{\partial H}{\partial\gamma}>0 .$$
--
--   Here $g$ stands for the semi-elasticity $(\partial\Pi^*/\partial s)(1/\Pi^*)$, which is positive for $0<s<\beta$ by Lemma 1 and does not depend on $\xi$ or $\gamma$. These signs drive the comparative statics of an interior equilibrium in Proposition 3.
--
--   **Formalization Note** The derivatives are taken with `deriv` and the conclusions are strict inequalities, so a junk value cannot satisfy them. The hypothesis $\xi<1$ is needed for $\partial H/\partial\gamma>0$ (at $\xi=1$ it is $0$). The proof's further clause "$\partial H/\partial s<0$ by the second order condition" is not posed.
-- source:
--   Denicolò & Panunzi, Common Ownership, Competition, and Corporate Governance, ECGI Finance Working Paper 927/2023 (SSRN 4523644, July 24, 2023; Management Science DOI 10.1287/mnsc.2023.03467), Appendix A, proof of Proposition 3, p. 39 (PDF p. 42); H from (A3), p. 38 (PDF p. 41)

import Mathlib
import Definitions.Def_CommonOwnership_Governance_Model

namespace CommonOwnership.Governance

/-- Proof of Proposition 3, p. 39: `∂H/∂ξ < 0` and `∂H/∂γ > 0` for `H` of (A3), when the
semi-elasticity `g = (∂Π*/∂s)(1/Π*)` is positive. -/
theorem eqA3_H_signs (β ξ γ s g : ℝ) (hβ : 0 < β) (hξ : 0 < ξ) (hξ1 : ξ < 1) (hγ : 0 < γ)
    (hg : 0 < g) :
    deriv (fun x => Hfun β x γ s g) ξ < 0 ∧ 0 < deriv (fun y => Hfun β ξ y s g) γ := by sorry

end CommonOwnership.Governance
