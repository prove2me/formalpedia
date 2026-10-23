-- Prove2me | Theorems.Thm_ContingentSourcing_Competition_proposition_3_i_ii
-- name    : ContingentSourcing.Competition.proposition_3_i_ii
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-22T17:30:57.94016+00:00
-- url     : https://prove2.me/theorems/c1dfaa64-cfa2-4ce9-9dbe-e81b4eab2051
-- title:
--   Proposition 3(i)–(ii), p. 18 — without shipment information and c_R > ψ_3, the equilibrium is sole sourcing from U or diversification; Table 3
-- statement:
--   Take no shipment information, $\rho=0$, and suppose $c_R>\psi_3=\frac{P_0+1}{P_1}c_U-P_0m$. Let $\phi_1=\frac{(1+P_0)m+c_U}{2}$, $\phi_2=\frac{2P_0m+c_U}{P_0+1}$, and define the Table 3 prices ($P_{0G}=P_0$, $P_{1G}=P_1$ at $\rho=0$):
--
--   | condition | $w_U^N$ | $w_R^N$ |
--   |---|---|---|
--   | (i-a) $c_R>\phi_1$ | $\frac{P_1m+c_U}{2P_1}$ | $c_R$ |
--   | (i-b) $\phi_2<c_R\le\phi_1$ | $\frac{c_R-P_{0G}m}{P_{1G}}$ | $c_R$ |
--   | (ii) $\psi_3<c_R\le\phi_2$ | $\frac{P_0m+c_R+2c_U/P_1}{3+P_0}$ | $\frac{2P_0m+2c_R+c_U}{3+P_0}$ |
--
--   Then the profile $(w_U^N,w_R^N,m)$ is an equilibrium, and every equilibrium $(w_U,w_R,w_E)$ has $w_U=w_U^N$ and:
--
--   1. if $c_R>\phi_2$, the buyer sources only from supplier U ($Q_R=0<Q_U$);
--   2. if $\psi_3<c_R\le\phi_2$, then $w_R=w_R^N$ and the buyer sources from both suppliers ($Q_U>0$, $Q_R>0$).
--
--   This is the no-information half of the comparison in Proposition 4.
--
--   **Formalization Note.** At $\rho=0$ the emergency price is irrelevant ($P_B=0$) and Table 3 lists none; the profile uses $w_E=m$ and the statement does not constrain $w_E$. In case (i) R receives no order and the paper writes $w_R^N=c_R$ by convention, so $w_R$ is not constrained there. Part (iii) ($c_R\le\psi_3$) is not stated.
-- source:
--   Lu & Tomlin, Forewarned Is Forearmed?, SSRN 4260604 author manuscript (1 May 2023) of MSOM doi:10.1287/msom.2021.0540, pp. 18–19 (PDF 18–19), Proposition 3(i)–(ii) and Table 3 rows (i-a), (i-b), (ii)

import Mathlib
import Definitions.Def_ContingentSourcing_Competition_Model

namespace ContingentSourcing.Competition

/-- Proposition 3(i)–(ii), p. 18, with Table 3 (i-a), (i-b), (ii): at ρ = 0 and c_R > ψ_3 the Table 3
profile is an equilibrium; every equilibrium has w_U = w_U^N, and the buyer sources only from U
(c_R > ϕ_2) or from both suppliers at w_R = w_R^N (c_R ≤ ϕ_2). -/
theorem proposition_3_i_ii (P : Params) (hP : P.Standing) (h : P.psi3 < P.cR) :
    P.IsEquilibrium 0 P.priceN ∧ ∀ w, P.IsEquilibrium 0 w →
      w.wU = P.priceN.wU ∧
      (P.phi2 < P.cR → (P.order 0 w).QR = 0 ∧ 0 < (P.order 0 w).QU) ∧
      (P.cR ≤ P.phi2 → w.wR = P.priceN.wR ∧ 0 < (P.order 0 w).QU ∧ 0 < (P.order 0 w).QR) := by sorry

end ContingentSourcing.Competition
