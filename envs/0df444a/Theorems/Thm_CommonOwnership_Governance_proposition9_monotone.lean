-- Prove2me | Theorems.Thm_CommonOwnership_Governance_proposition9_monotone
-- name    : CommonOwnership.Governance.proposition9_monotone
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-14T03:09:47.009183+00:00
-- url     : https://prove2.me/theorems/791cf0d8-ebd0-43b6-9e91-f0d15c58f461
-- title:
--   Proposition 9, p. 28 (PDF p. 31) — with blockholder diversion, equilibrium common ownership is increasing in φ
-- statement:
--   Let $0<\theta\le1$ and $0<\beta\le1$, and let industry profit be $\Pi^*(s)=P(\lambda(s))$ with $P(\lambda)>0$ for all $\lambda\in[0,1]$, the same for all values of $\varphi$. In the variant of §7.1, the blockholder diverts a fraction $a$ of profits at deadweight loss $D(a)=\tfrac12\varphi a^2$. For $\varphi\ge1$, let $a^*$ be an optimal diversion rule (for every $s\in[0,\beta]$, $a^*(s)\in[0,1]$ maximizes $a+(\beta-s)(1-a)-\tfrac12\varphi a^2$ over $a\in[0,1]$), and call $s^*$ an equilibrium if it maximizes over $[0,\beta]$ the joint surplus
--   $$S(s)=\Big(a^*(s)+\beta[1-a^*(s)]-\tfrac12\varphi\,a^*(s)^2\Big)\,P(\lambda(s)).$$
--   If $1\le\varphi_1<\varphi_2$, every equilibrium $s_1^*$ at $\varphi_1$ and every equilibrium $s_2^*$ at $\varphi_2$ satisfy
--   $$s_1^*\le s_2^* .$$
--
--   Since $\varphi$ measures how hard it is for the blockholder to dilute minority shareholders, better corporate governance leads to more common ownership.
--
--   **Formalization Note** The surplus is built from (43) and any optimal diversion rule, never from the printed closed form (47), which carries an extra factor $(1-\beta)$. The bound $\varphi\ge1$ is a disclosed pin (interior $a^*$). Monotonicity is weak and holds for every pair of equilibria.
-- source:
--   Denicolò & Panunzi, Common Ownership, Competition, and Corporate Governance, ECGI Finance Working Paper 927/2023 (SSRN 4523644, July 24, 2023; Management Science DOI 10.1287/mnsc.2023.03467), p. 28 (PDF p. 31), Proposition 9; proof Appendix A, p. 41 (PDF p. 44)

import Mathlib
import Definitions.Def_CommonOwnership_Governance_Model
import Definitions.Def_CommonOwnership_Governance_DiversionModel

namespace CommonOwnership.Governance

/-- Proposition 9, p. 28: in the §7.1 variant (blockholder diversion with deadweight loss
`½ φ a²`), the equilibrium level of common ownership is monotonically increasing in `φ`. -/
theorem proposition9_monotone (θ β : ℝ) (hθ : 0 < θ) (hθ1 : θ ≤ 1) (hβ : 0 < β) (hβ1 : β ≤ 1)
    (P : ℝ → ℝ) (hP : ∀ l ∈ Set.Icc (0:ℝ) 1, 0 < P l)
    (φ₁ φ₂ : ℝ) (hφ₁ : 1 ≤ φ₁) (hφ : φ₁ < φ₂) (a₁ a₂ : ℝ → ℝ)
    (ha₁ : IsOptDiversion (divCost φ₁) β a₁) (ha₂ : IsOptDiversion (divCost φ₂) β a₂)
    (s₁ s₂ : ℝ)
    (hs₁ : IsEqOwnership (jointSurplusDiv (divCost φ₁) a₁ P θ β) β s₁)
    (hs₂ : IsEqOwnership (jointSurplusDiv (divCost φ₂) a₂ P θ β) β s₂) : s₁ ≤ s₂ := by sorry

end CommonOwnership.Governance
