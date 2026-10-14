-- Prove2me | Theorems.Thm_CommonOwnership_Governance_eqA5_K_signs
-- name    : CommonOwnership.Governance.eqA5_K_signs
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-14T03:08:50.396947+00:00
-- url     : https://prove2.me/theorems/edbdd48b-b504-4ea8-8286-bdd5512e3bb4
-- title:
--   Proof of Proposition 3, p. 39 (PDF p. 42) — ∂K/∂ξ < 0 and ∂K/∂γ > 0
-- statement:
--   Let $\beta>0$, $0<\xi<1$, $\gamma>0$, and let $\Pi^*_0<\Pi^*_+$ with $\Pi^*_+>0$. For the function of (A5),
--   $$K(\xi,\gamma)=\Big[2\gamma\beta\frac{1-\xi}{\xi^2}+\beta^2\Big]\frac{\Pi^*_+-\Pi^*_0}{\Pi^*_+}-s^{+2},$$
--   we have
--   $$\frac{\partial K}{\partial\xi}<0,\qquad\frac{\partial K}{\partial\gamma}>0 .$$
--
--   Industry profits at $s^+>0$ exceed those at $s=0$ by Lemma 1, and they do not depend on $\xi$ or $\gamma$. These signs give the direction of the jumps of the equilibrium between $0$ and $s^+$ in Proposition 3.
--
--   **Formalization Note** The derivatives are taken with `deriv` and the conclusions are strict inequalities. The ordering $\Pi^*_0<\Pi^*_+$ is a hypothesis. The proof's "$\propto$" statements about $\partial\Delta S$ are not posed.
-- source:
--   Denicolò & Panunzi, Common Ownership, Competition, and Corporate Governance, ECGI Finance Working Paper 927/2023 (SSRN 4523644, July 24, 2023; Management Science DOI 10.1287/mnsc.2023.03467), Appendix A, proof of Proposition 3, p. 39 (PDF p. 42); K from (A5)

import Mathlib
import Definitions.Def_CommonOwnership_Governance_Model

namespace CommonOwnership.Governance

/-- Proof of Proposition 3, p. 39: `∂K/∂ξ < 0` and `∂K/∂γ > 0` for `K` of (A5), when industry
profit is positive at `s⁺` and higher there than at `s = 0` (`0 < Π*₊`, `Π*₀ < Π*₊`). -/
theorem eqA5_K_signs (β ξ γ sp Pi0 Pip : ℝ) (hβ : 0 < β) (hξ : 0 < ξ) (hξ1 : ξ < 1)
    (hγ : 0 < γ) (hPip : 0 < Pip) (hgain : Pi0 < Pip) :
    deriv (fun x => Kfun β x γ sp Pi0 Pip) ξ < 0 ∧
      0 < deriv (fun y => Kfun β ξ y sp Pi0 Pip) γ := by sorry

end CommonOwnership.Governance
