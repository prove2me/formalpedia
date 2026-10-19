-- Prove2me | Theorems.Thm_DataGrowth_BGP_eq_A_15
-- name    : DataGrowth.BGP.eq_A_15
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-18T20:10:14.173974+00:00
-- url     : https://prove2.me/theorems/6a4ceaf3-473b-41d8-bb73-198e2b1b960b
-- title:
--   (A.15), PDF p. 28 — planner BGP rates $g^*_S=\sigma n/((1-\zeta)\sigma-\xi(1-\gamma))$
-- statement:
--   Assume the standing parameter ranges and let a balanced growth path of the planner's necessary-condition system be given, with growth rates $g_c,g_N,g_\phi$. Write $D=(1-\zeta)\sigma-\xi(1-\gamma)$. Then
--   $$
--   g_c=g_N=g^*_S=\frac{\sigma}{D}\,n,\qquad g_\phi=\frac{1-\gamma}{D}\,n .
--   $$
--
--   These are the same rates as in the decentralized economy (Proposition 1). The paper states (A.15) for $g^*_S=\dot N/N$ and adds that "the growth rates of other related variables can be derived similarly"; consumption and data per capita are included here.
--
--   **Formalization Note** The labor shares have rate zero by Lemma A.1. The hypothesis $\gamma>1$ is not needed. The planner's economy is its Hamiltonian necessary-condition system.
-- source:
--   Cong, Xie, Zhang, Knowledge Accumulation, Privacy, and Growth in a Data Economy, arXiv:2109.10028v1, p. 28 (Online Appendix p. 5), (A.15)

import Mathlib
import Definitions.Def_DataGrowth_BGP_Planner

namespace DataGrowth.BGP

/-- Cong, Xie, Zhang, *Knowledge Accumulation, Privacy, and Growth in a Data Economy*, arXiv:2109.10028v1, PDF p. 28 (Online Appendix p. 5), (A.15): on a balanced growth path of the
planner's necessary-condition system the growth rate is g*_S = σn/((1 − ζ)σ − ξ(1 − γ)), the same
as in the decentralized model, and "the growth rates of other related variables can be derived
similarly": consumption grows at g*_S and data per capita at (1 − γ)n/((1 − ζ)σ − ξ(1 − γ)).

Formalization Note: g*_S is the growth rate Ṅ/N of (A.14) (per-capita output y_S = A N l_E); the
"other related variables" are c and ϕ (l_R and l_E have rate zero by Lemma A.1). γ > 1 is not used.
The planner's economy is encoded by the Hamiltonian necessary conditions (`IsPlanEq`); the optimal
control problem (24) is not formalized. -/
theorem eq_A_15 (P : Params) (hP : P.Standing) (S : PlanPath) (Q : PlanRates)
    (hS : IsPlanBGP P S Q) :
    Q.gc = P.gStar ∧ Q.gN = P.gStar ∧ Q.gphi = P.gPhiStar := by sorry

end DataGrowth.BGP
