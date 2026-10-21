-- Prove2me | Theorems.Thm_DataGrowth_BGP_eq_A_13
-- name    : DataGrowth.BGP.eq_A_13
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-18T20:10:14.025093+00:00
-- url     : https://prove2.me/theorems/77aa5927-50a9-49aa-b959-9f2011bd6986
-- title:
--   (A.13), PDF p. 27 — planner BGP: $(\zeta-1)g_N+\xi g_\phi+n=0$
-- statement:
--   Assume the standing parameter ranges and let a balanced growth path of the planner's necessary-condition system be given, with growth rates $g_N,g_\phi$. Then
--   $$
--   (\zeta-1)\,g_N+\xi\,g_\phi+n=0 .
--   $$
--
--   It comes from the costate equation (A.10) for varieties combined with (A.9): the combination (A.12) has a constant right-hand side, so its left-hand side $N^{\zeta-1}\phi^\xi L$ times constants is constant. It is the same relation as (A.3) in the decentralized economy.
--
--   **Formalization Note** The planner's economy is its Hamiltonian necessary-condition system; the optimal control problem (24) is not formalized.
-- source:
--   Cong, Xie, Zhang, Knowledge Accumulation, Privacy, and Growth in a Data Economy, arXiv:2109.10028v1, p. 27 (Online Appendix p. 4), (A.13)

import Mathlib
import Definitions.Def_DataGrowth_BGP_Planner

namespace DataGrowth.BGP

/-- Cong, Xie, Zhang, *Knowledge Accumulation, Privacy, and Growth in a Data Economy*, arXiv:2109.10028v1, PDF p. 27 (Online Appendix p. 4), (A.13): on a balanced growth path of the
planner's necessary-condition system, (ζ − 1) Ṅ/N + ξ ϕ̇/ϕ + n = 0.

Formalization Note: the planner's economy is encoded by the current-value Hamiltonian's necessary
conditions (25)–(27), (A.7)–(A.10) (`IsPlanEq`); the optimal control problem (24) is not
formalized, and the planner's BGP is a BGP of this system (`IsPlanBGP`, t > 0). The combined
identity (A.12) is a step of the proof. -/
theorem eq_A_13 (P : Params) (hP : P.Standing) (S : PlanPath) (Q : PlanRates)
    (hS : IsPlanBGP P S Q) :
    (P.ζ - 1) * Q.gN + P.ξ * Q.gphi + P.n = 0 := by sorry

end DataGrowth.BGP
