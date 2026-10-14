-- Prove2me | Theorems.Thm_CommonOwnership_Governance_proposition2_partial
-- name    : CommonOwnership.Governance.proposition2_partial
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-14T03:08:52.21834+00:00
-- url     : https://prove2.me/theorems/2edb761d-0168-48e5-8cf0-45945a7b1f2d
-- title:
--   Proposition 2, p. 15 (PDF p. 18) — common ownership is always partial: 0 ≤ s* < β
-- statement:
--   Let $0<\theta\le1$, $0<\beta\le1$ and $0<\xi<1$. Let the monitoring cost $C$ be twice continuously differentiable with
--   $$C(0)=0,\qquad C'(0)=0,\qquad C'(1)>\xi,\qquad C''(m)>0\ \text{ for } m\in[0,1].$$
--   Let $m^*$ be an optimal monitoring rule (for every residual stake $t\in[0,\beta]$, $m^*(t)\in[0,1]$ maximizes $t[1-\xi(1-m)]-C(m)$ over $m\in[0,1]$), and let industry profit be $\Pi^*(s)=P(\lambda(s))$ with $P$ differentiable at $\lambda=1$ and $P(1)>0$. If $s^*$ is an equilibrium level of common ownership, that is, $s^*\in[0,\beta]$ maximizes the joint surplus $S(s)=\nu^*(s)\Pi^*(s)$ of (13)–(14) over $[0,\beta]$, then
--   $$0\le s^*<\beta .$$
--
--   The investor never buys out the blockholders: at $s=\beta$ the marginal benefit of common ownership (higher industry profit) vanishes while the marginal cost (weaker monitoring) does not.
--
--   **Formalization Note** The paper calls $C$ increasing and convex; the statement assumes $C''>0$ on $[0,1]$ because the paper divides by $C''(m^*)$ in (19) and in the proof. Profits are assumed twice continuously differentiable in the paper (p. 9) and positive; here only differentiability of $P$ at $\lambda=1$ and $P(1)>0$ are used. The bounds $\theta\le1$, $\beta\le1$, $\xi<1$ are the paper's standing assumptions.
-- source:
--   Denicolò & Panunzi, Common Ownership, Competition, and Corporate Governance, ECGI Finance Working Paper 927/2023 (SSRN 4523644, July 24, 2023; Management Science DOI 10.1287/mnsc.2023.03467), p. 15 (PDF p. 18), Proposition 2; proof Appendix A, p. 38 (PDF p. 41); assumptions on C, p. 7 (PDF p. 10)

import Mathlib
import Definitions.Def_CommonOwnership_Governance_Model

namespace CommonOwnership.Governance

/-- Proposition 2, p. 15: common ownership is always partial, `0 ≤ s* < β`, for a general
monitoring cost `C` with `C(0) = 0`, `C'(0) = 0`, `C'(1) > ξ` and `C'' > 0` on `[0, 1]`. -/
theorem proposition2_partial (θ β ξ : ℝ) (hθ : 0 < θ) (hθ1 : θ ≤ 1) (hβ : 0 < β) (hβ1 : β ≤ 1)
    (hξ : 0 < ξ) (hξ1 : ξ < 1)
    (C : ℝ → ℝ) (hC : ContDiff ℝ 2 C) (hC0 : C 0 = 0) (hC'0 : deriv C 0 = 0)
    (hC'1 : ξ < deriv C 1) (hC'' : ∀ m ∈ Set.Icc (0:ℝ) 1, 0 < deriv (deriv C) m)
    (mstar : ℝ → ℝ) (hm : IsOptMonitoring C ξ β mstar)
    (P : ℝ → ℝ) (hPd : DifferentiableAt ℝ P 1) (hP1 : 0 < P 1)
    (s : ℝ) (hs : IsEqOwnership (jointSurplus C mstar P θ β ξ) β s) : 0 ≤ s ∧ s < β := by sorry

end CommonOwnership.Governance
