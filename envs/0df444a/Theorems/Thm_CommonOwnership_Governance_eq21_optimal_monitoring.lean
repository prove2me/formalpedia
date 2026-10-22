-- Prove2me | Theorems.Thm_CommonOwnership_Governance_eq21_optimal_monitoring
-- name    : CommonOwnership.Governance.eq21_optimal_monitoring
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-14T03:08:44.173313+00:00
-- url     : https://prove2.me/theorems/d812399d-c03f-4b6e-9703-cbde0e14fc09
-- title:
--   (21), p. 17 (PDF p. 20), with (7), p. 10 — under C(m) = ½γm² the blockholder's optimal monitoring is m* = ξ(β − s)/γ
-- statement:
--   Let $0<\beta\le1$, $\xi>0$ and $\gamma>\xi$, and let the monitoring cost be quadratic, $C(m)=\tfrac12\gamma m^2$. A blockholder with residual stake $t=\beta-s\in[0,\beta]$ chooses monitoring $m\in[0,1]$ to maximize
--   $$t\,[1-\xi(1-m)]-\tfrac12\gamma m^2 .$$
--   Then the rule
--   $$m^*(t)=\frac{\xi t}{\gamma},\qquad\text{i.e.}\qquad m^*=\frac{\xi(\beta-s)}{\gamma},$$
--   is an optimal monitoring rule, and every optimal monitoring rule coincides with it on $[0,\beta]$.
--
--   This is the closed form (21) of the first-order condition (7), $C'(m)=(\beta-s)\xi$. It connects the abstract optimality predicate used in Proposition 3 with the explicit surplus of Appendix A.
--
--   **Formalization Note** The condition $\gamma>\xi$ is footnote 19's form of $C'(1)>\xi$; with $\beta\le1$ it puts $m^*$ inside $[0,1]$. The statement asserts both existence (the formula is optimal) and uniqueness on $t\in[0,\beta]$.
-- source:
--   Denicolò & Panunzi, Common Ownership, Competition, and Corporate Governance, ECGI Finance Working Paper 927/2023 (SSRN 4523644, July 24, 2023; Management Science DOI 10.1287/mnsc.2023.03467), p. 17 (PDF p. 20), (20), (21), footnote 19; p. 10 (PDF p. 13), §3.2.1, (7)

import Mathlib
import Definitions.Def_CommonOwnership_Governance_Model

namespace CommonOwnership.Governance

/-- (7), p. 10, and (21), p. 17: under the quadratic cost (20), the blockholder's optimal monitoring
at residual stake `t = β − s ∈ [0, β]` exists, is unique, and equals `ξ t / γ`. -/
theorem eq21_optimal_monitoring (β ξ γ : ℝ) (hβ : 0 < β) (hβ1 : β ≤ 1) (hξ : 0 < ξ)
    (hγ : ξ < γ) :
    IsOptMonitoring (quadCost γ) ξ β (fun t => ξ * t / γ) ∧
      ∀ mstar : ℝ → ℝ, IsOptMonitoring (quadCost γ) ξ β mstar →
        ∀ t ∈ Set.Icc (0:ℝ) β, mstar t = ξ * t / γ := by sorry

end CommonOwnership.Governance
