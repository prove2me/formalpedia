-- Prove2me | Theorems.Thm_DataGrowth_BGP_proposition_3
-- name    : DataGrowth.BGP.proposition_3
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-18T20:10:27.163409+00:00
-- url     : https://prove2.me/theorems/3978e349-2b4e-4370-9472-67f1a1974704
-- title:
--   Proposition 3, p. 11 — with $\gamma>1$, the planner's BGP growth rates equal the decentralized economy's
-- statement:
--   Assume the standing parameter ranges and $\gamma>1$. Take, for the same parameters, a balanced growth path of the decentralized economy with growth rates $g_c,g_N,g_\phi,g_{l_R},g_{l_E}$, and a balanced growth path of the social planner's necessary-condition system with growth rates $g^S_c,g^S_N,g^S_\phi,g^S_{l_R},g^S_{l_E}$. Then
--   $$
--   g^S_c=g_c,\quad g^S_N=g_N,\quad g^S_\phi=g_\phi,\quad g^S_{l_R}=g_{l_R},\quad g^S_{l_E}=g_{l_E},
--   $$
--   and the planner's per-capita output $y_S(t)=AN(t)l_E(t)$ of (A.14) grows at the decentralized rate $g_c=g_y$.
--
--   So the decentralized economy, despite monopolistic competition and the knowledge spillover, grows at the socially optimal rate on the balanced growth path; the inefficiency shows only in levels (the R&D labor share and the data intensity), not in growth rates.
--
--   **Formalization Note** The decentralized economy is given by its level-form equilibrium conditions (4), (5), (3) with $s=0$, (9), (13), (15), (17)–(19), and $l_E+l_R=1$; the planner's economy by the current-value Hamiltonian's necessary conditions (25)–(27), (A.7)–(A.10), and the optimal control problem (24) itself is not formalized. A balanced growth path has each variable at a constant rate of its own. The hypothesis $\gamma>1$ is kept as printed; the growth-rate comparison does not use it.
-- source:
--   Cong, Xie, Zhang, Knowledge Accumulation, Privacy, and Growth in a Data Economy, arXiv:2109.10028v1, p. 11, Proposition 3

import Mathlib
import Definitions.Def_DataGrowth_BGP_DecEconomy
import Definitions.Def_DataGrowth_BGP_Planner

namespace DataGrowth.BGP

/-- Cong, Xie, Zhang, *Knowledge Accumulation, Privacy, and Growth in a Data Economy*, arXiv:2109.10028v1, p. 11, Proposition 3: with γ > 1, the balanced-growth-path growth rates in the
social planner's problem are the same as those in the decentralized economy.

For the same parameters, take a balanced growth path of the decentralized economy and one of the
planner's economy. Their growth rates of consumption c, varieties N, data per capita ϕ and the
labor shares l_R, l_E coincide, and per-capita output of the planner's economy, y_S = A N l_E
((A.14), PDF p. 28), grows at the decentralized rate g*_c = g*_y.

Formalization Note:
* The decentralized economy is encoded by its level-form equilibrium conditions (`IsDecEq`:
  (3) with s = 0, (4), (5), (9), (13), (15), (17)–(19), l_E + l_R = 1, θ = 0); its BGP
  (`IsDecBGP`) has each variable at its own constant rate, r constant and g_c = g_y.
* The planner's economy is encoded by the current-value Hamiltonian's necessary conditions
  (25)–(27), (A.7)–(A.10) (`IsPlanEq`); the optimal control problem (24) itself is not formalized,
  and the planner's BGP is a BGP of this system (`IsPlanBGP`).
* Time runs over t > 0. The hypothesis γ > 1 is kept as printed, although the growth-rate
  comparison does not use it (it guarantees, via (29), that a planner BGP with an admissible R&D
  share exists). -/
theorem proposition_3 (P : Params) (hP : P.Standing) (hγ : 1 < P.γ)
    (E : DecPath) (R : DecRates) (hE : IsDecBGP P E R)
    (S : PlanPath) (Q : PlanRates) (hS : IsPlanBGP P S Q) :
    Q.gc = R.gc ∧ Q.gN = R.gN ∧ Q.gphi = R.gphi ∧ Q.glR = R.glR ∧ Q.glE = R.glE ∧
      HasConstGrowth (fun t => P.Aconst * S.N t * S.lE t) R.gc := by sorry

end DataGrowth.BGP
