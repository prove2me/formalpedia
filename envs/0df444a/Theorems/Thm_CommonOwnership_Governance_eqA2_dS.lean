-- Prove2me | Theorems.Thm_CommonOwnership_Governance_eqA2_dS
-- name    : CommonOwnership.Governance.eqA2_dS
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-14T03:08:54.034983+00:00
-- url     : https://prove2.me/theorems/22b07a32-eb8c-4b5e-b51e-06f48c1de5fb
-- title:
--   (A2)–(A3), p. 38 (PDF p. 41) — under (20)–(21), ∂S/∂s = (ξ²/γ)HΠ*
-- statement:
--   Let $\xi>0$ and $\gamma>0$. With the quadratic cost $C(m)=\tfrac12\gamma m^2$ and the monitoring rule $m^*=\xi(\beta-s)/\gamma$ of (21), let
--   $$S(s)=\Big(\beta\{1-\xi[1-m^*]\}-C(m^*)\Big)\,\Pi^*(s)$$
--   for an industry-profit path $\Pi^*$. If $\Pi^*$ is differentiable at $s$ with derivative $d$ and $\Pi^*(s)\neq0$, then $S$ is differentiable at $s$ and
--   $$\frac{\partial S}{\partial s}=\frac{\xi^2}{\gamma}\,H\,\Pi^*,\qquad H=-s+\Big[\gamma\beta\frac{1-\xi}{\xi^2}+\tfrac12(\beta^2-s^2)\Big]\frac{\partial\Pi^*}{\partial s}\frac{1}{\Pi^*},$$
--   with $\partial\Pi^*/\partial s=d$.
--
--   The sign of $\partial S/\partial s$ is that of $H$; an interior equilibrium solves $H=0$, which is the equation the comparative statics of Proposition 3 differentiate.
--
--   **Formalization Note** $\Pi^*$ is an arbitrary function of $s$ (in the model, $P(\lambda(s))$); it does not depend on $\xi$ or $\gamma$.
-- source:
--   Denicolò & Panunzi, Common Ownership, Competition, and Corporate Governance, ECGI Finance Working Paper 927/2023 (SSRN 4523644, July 24, 2023; Management Science DOI 10.1287/mnsc.2023.03467), Appendix A, proof of Proposition 3, p. 38 (PDF p. 41), (A2), (A3)

import Mathlib
import Definitions.Def_CommonOwnership_Governance_Model

namespace CommonOwnership.Governance

/-- (A2)–(A3), p. 38: under (20)–(21), `∂S/∂s = (ξ²/γ) H Π*` with `H` of (A3) evaluated at the
semi-elasticity `(∂Π*/∂s)(1/Π*)`. -/
theorem eqA2_dS (β ξ γ s : ℝ) (hξ : 0 < ξ) (hγ : 0 < γ) (Pi_ : ℝ → ℝ) (d : ℝ)
    (hd : HasDerivAt Pi_ d s) (hPi : Pi_ s ≠ 0) :
    HasDerivAt (surplusQ β ξ γ Pi_) (ξ ^ 2 / γ * Hfun β ξ γ s (d / Pi_ s) * Pi_ s) s := by sorry

end CommonOwnership.Governance
