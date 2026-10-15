-- Prove2me | Theorems.Thm_CommonOwnership_Governance_proposition3_monotone
-- name    : CommonOwnership.Governance.proposition3_monotone
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-14T03:08:50.092988+00:00
-- url     : https://prove2.me/theorems/3b98fd05-8d56-4907-92e2-f9f7561dcca2
-- title:
--   Proposition 3, p. 17 (PDF p. 20) — equilibrium common ownership is decreasing in ξ and increasing in γ
-- statement:
--   Let $0<\theta\le1$ and $0<\beta\le1$, let the monitoring cost be quadratic, $C(m)=\tfrac12\gamma m^2$, and let industry profit be $\Pi^*(s)=P(\lambda(s))$, where $\lambda$ is the common-ownership weight (17) and $P$ is a function with $P(\lambda)>0$ for all $\lambda\in[0,1]$, the same for all values of $\xi$ and $\gamma$.
--
--   For parameters $(\xi,\gamma)$ with $0<\xi<1$ and $\gamma>\xi$, let $m^*$ be an optimal monitoring rule (for every $t\in[0,\beta]$, $m^*(t)\in[0,1]$ maximizes $t[1-\xi(1-m)]-\tfrac12\gamma m^2$ over $m\in[0,1]$), and call $s^*$ an equilibrium level of common ownership if $s^*\in[0,\beta]$ maximizes over $[0,\beta]$ the joint surplus
--   $$S(s)=\Big(\beta\{1-\xi[1-m^*(\beta-s)]\}-\tfrac12\gamma\,m^*(\beta-s)^2\Big)\,P(\lambda(s)).$$
--   Then:
--
--   1. **Decreasing in $\xi$.** If $0<\xi_1<\xi_2<1$ and $\gamma>\xi_2$, every equilibrium $s_2^*$ at $(\xi_2,\gamma)$ and every equilibrium $s_1^*$ at $(\xi_1,\gamma)$ satisfy $$s_2^*\le s_1^* .$$
--   2. **Increasing in $\gamma$.** If $0<\xi<1$ and $\xi<\gamma_1<\gamma_2$, every equilibrium $s_1^*$ at $(\xi,\gamma_1)$ and every equilibrium $s_2^*$ at $(\xi,\gamma_2)$ satisfy $$s_1^*\le s_2^* .$$
--
--   Fewer opportunities for managers to divert profits (lower $\xi$) raise common ownership, while cheaper monitoring (lower $\gamma$) lowers it, although both improve corporate governance.
--
--   **Formalization Note** Equilibrium ownership is taken, as in §4.2, to be a maximizer of the symmetric surplus (13) over $[0,\beta]$; Proposition 1 (the bargaining reduction) and §4.2's concavity remark are not assumed. Industry profit enters through an arbitrary positive function $P$ of $\lambda$, so the theorem covers the equilibrium industry profit of every product-market model of §3.1.3. Monitoring is any optimal rule at each parameter value, not the closed form (21). Monotonicity is weak and holds for every pair of equilibria, since the equilibrium can be $0$ at both parameter values. The bound $\theta\le1$ is the paper's assumption; $\xi<1$ (a fraction) and positivity of $P$ are disclosed pins.
-- source:
--   Denicolò & Panunzi, Common Ownership, Competition, and Corporate Governance, ECGI Finance Working Paper 927/2023 (SSRN 4523644, July 24, 2023; Management Science DOI 10.1287/mnsc.2023.03467), p. 17 (PDF p. 20), Proposition 3; proof Appendix A, pp. 38–39 (PDF pp. 41–42)

import Mathlib
import Definitions.Def_CommonOwnership_Governance_Model

namespace CommonOwnership.Governance

/-- Proposition 3, p. 17: under the quadratic cost (20), the equilibrium level of common
ownership is monotonically decreasing in `ξ` and monotonically increasing in `γ`: every
equilibrium stake at the larger `ξ` is at most every equilibrium stake at the smaller `ξ`
(`γ` fixed), and every equilibrium stake at the larger `γ` is at least every equilibrium
stake at the smaller `γ` (`ξ` fixed). Monitoring is the blockholder's optimum at each
parameter value; industry profit `P(λ)` is one positive function of `λ` shared by both. -/
theorem proposition3_monotone (θ β : ℝ) (hθ : 0 < θ) (hθ1 : θ ≤ 1) (hβ : 0 < β) (hβ1 : β ≤ 1)
    (P : ℝ → ℝ) (hP : ∀ l ∈ Set.Icc (0:ℝ) 1, 0 < P l) :
    (∀ (ξ₁ ξ₂ γ : ℝ) (m₁ m₂ : ℝ → ℝ) (s₁ s₂ : ℝ),
      0 < ξ₁ → ξ₁ < ξ₂ → ξ₂ < 1 → ξ₂ < γ →
      IsOptMonitoring (quadCost γ) ξ₁ β m₁ → IsOptMonitoring (quadCost γ) ξ₂ β m₂ →
      IsEqOwnership (jointSurplus (quadCost γ) m₁ P θ β ξ₁) β s₁ →
      IsEqOwnership (jointSurplus (quadCost γ) m₂ P θ β ξ₂) β s₂ → s₂ ≤ s₁) ∧
    (∀ (ξ γ₁ γ₂ : ℝ) (m₁ m₂ : ℝ → ℝ) (s₁ s₂ : ℝ),
      0 < ξ → ξ < 1 → ξ < γ₁ → γ₁ < γ₂ →
      IsOptMonitoring (quadCost γ₁) ξ β m₁ → IsOptMonitoring (quadCost γ₂) ξ β m₂ →
      IsEqOwnership (jointSurplus (quadCost γ₁) m₁ P θ β ξ) β s₁ →
      IsEqOwnership (jointSurplus (quadCost γ₂) m₂ P θ β ξ) β s₂ → s₁ ≤ s₂) := by sorry

end CommonOwnership.Governance
