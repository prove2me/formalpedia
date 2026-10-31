-- Prove2me | Theorems.Thm_ContingentSourcing_Competition_proposition_3_i_ii_corrected
-- name    : ContingentSourcing.Competition.proposition_3_i_ii_corrected
-- status  : Proved
-- author  : @tianyipeng
-- created : 2026-10-30T06:43:53.844038+00:00
-- url     : https://prove2.me/theorems/d2f2acd0-0b3c-46bd-a2a3-c445fcd8baa8
-- title:
--   Proposition 3(i)–(ii), p. 18 (boundary-corrected) — without shipment information and c_R > ψ_3, sole sourcing from U or diversification at the Table 3 prices
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
--   1. if $c_R\ge\phi_2$, the buyer sources only from supplier U ($Q_R=0<Q_U$);
--   2. if $\psi_3<c_R<\phi_2$, then $w_R=w_R^N$ and the buyer sources from both suppliers ($Q_U>0$, $Q_R>0$).
--
--   **Formalization Note.** This is the original milestone `proposition_3_i_ii` with the boundary $c_R=\phi_2$ moved from case (ii) to case (i). As printed, the (ii) claim $Q_R>0$ fails at $c_R=\phi_2$. There the (ii) prices coincide with the (i-b) prices, $w_R^N=c_R=\eta_1$, and the buyer's order has $Q_R=0$; for example $m=10$, $P_1=1/2$, $c_U=0$, $c_R=20/3$ (see the disproof of `proposition_3_i_ii`). The emergency price is irrelevant at $\rho=0$ and the profile uses $w_E=m$. In case (i) R receives no order and $w_R$ is not constrained. Part (iii) is not stated.
-- source:
--   Lu & Tomlin, Forewarned Is Forearmed?, SSRN 4260604 author manuscript (1 May 2023) of MSOM doi:10.1287/msom.2021.0540, pp. 18–19 (PDF 18–19), Proposition 3(i)–(ii) and Table 3 rows (i-a), (i-b), (ii); boundary c_R = ϕ_2 corrected

import Mathlib
import Definitions.Def_ContingentSourcing_Competition_Model

namespace ContingentSourcing.Competition

/-- Proposition 3(i)–(ii), p. 18, with Table 3, boundary-corrected: at ρ = 0 and c_R > ψ_3 the Table 3
profile is an equilibrium; every equilibrium has w_U = w_U^N, and the buyer sources only from U
(c_R ≥ ϕ_2) or from both suppliers at w_R = w_R^N (c_R < ϕ_2). -/
theorem proposition_3_i_ii_corrected (P : Params) (hP : P.Standing) (h : P.psi3 < P.cR) :
    P.IsEquilibrium 0 P.priceN ∧ ∀ w, P.IsEquilibrium 0 w →
      w.wU = P.priceN.wU ∧
      (P.phi2 ≤ P.cR → (P.order 0 w).QR = 0 ∧ 0 < (P.order 0 w).QU) ∧
      (P.cR < P.phi2 → w.wR = P.priceN.wR ∧ 0 < (P.order 0 w).QU ∧ 0 < (P.order 0 w).QR) := by sorry

end ContingentSourcing.Competition
