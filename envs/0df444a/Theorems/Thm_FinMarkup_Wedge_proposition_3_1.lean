-- Prove2me | Theorems.Thm_FinMarkup_Wedge_proposition_3_1
-- name    : FinMarkup.Wedge.proposition_3_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-20T20:38:37.808889+00:00
-- url     : https://prove2.me/theorems/75f9c9ab-aa8f-47ab-84e9-711f925d1aa3
-- title:
--   Proposition 3.1 — optimal markup equals η/(η−1) times one minus the wedge
-- statement:
--   Consider one firm at one instant. Assume $1<\epsilon<\eta$, customer accumulation $\beta\ge0$, productivity $A>0$, rental rate $R>0$, industry price index $P_t>0$, customer base $M>0$, marginal customer-base value $\mu\ge0$, and marginal liquidity value $\nu>0$. Define $\Omega=(\beta A/R)(\mu/\nu)$ and suppose $\Omega<1$. Then $\Omega\ge0$, and for every positive price $P$,
--
--   $$P\text{ globally maximizes }\mu g_M(P)+\nu g_W(P)\text{ over positive prices}
--     \quad\Longleftrightarrow\quad
--     \Lambda(P)=\frac{\eta}{\eta-1}(1-\Omega).$$
--
--   Thus the markup of the optimal firm price is the usual constant-elasticity markup reduced by the customer-base wedge. The equivalence also determines the optimal positive price uniquely.
--
--   **Formalization Note** The source's equilibrium proposition is expressed as an exact characterization of maximizers of the price-dependent Hamiltonian from its customer and cash drifts. Brownian and payout terms do not depend on the price. The assumption $\Omega<1$ ensures a positive finite maximizer exists; otherwise the objective is unbounded as $P\downarrow0$. The paper states $\beta>0$ but discusses the boundary $\beta=0$, which this statement includes. Its discussion has $\nu\ge1$; positivity alone is sufficient here. Positivity of $A,R,P_t,M$ is implicit in the model's economic quantities. Time and firm indices are suppressed.
-- source:
--   Dou & Ji, External Financing and Customer Capital: A Financial Theory of Markups, SSRN 2574953 (version of May 11, 2020), p. 14 (PDF 15), Proposition 3.1, (3.1)–(3.2); Online Appendix A.1, pp. 33–34 (PDF 34–35)

import Mathlib
import Definitions.Def_FinMarkup_Wedge_Model

namespace FinMarkup.Wedge

/-- Proposition 3.1, p. 14: the optimal markup and its nonnegative wedge. -/
theorem proposition_3_1 (m : Params) (hS : m.Standing) (Pt M W mu nu : ℝ)
    (hPt : 0 < Pt) (hM : 0 < M) (hmu : 0 ≤ mu) (hnu : 0 < nu)
    (hΩ : wedge m mu nu < 1) :
    0 ≤ wedge m mu nu ∧
    ∀ p : ℝ, 0 < p →
      (IsOptimalPrice m Pt M W mu nu p ↔
        markup m p = m.eta / (m.eta - 1) * (1 - wedge m mu nu)) := by sorry

end FinMarkup.Wedge
