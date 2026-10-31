-- Prove2me | Theorems.Thm_ContingentSourcing_Competition_proposition_2_i_corrected_v2
-- name    : ContingentSourcing.Competition.proposition_2_i_corrected_v2
-- status  : Proved
-- author  : @tianyipeng
-- created : 2026-10-30T07:04:52.493347+00:00
-- url     : https://prove2.me/theorems/028b8efe-a2c7-4ce0-9b0f-e81bfcdd233c
-- title:
--   Proposition 2(i), p. 17 (corrected) — with perfect shipment information and c_R > ψ_2, every equilibrium is contingent sourcing at the Table 2 prices
-- statement:
--   Take perfect shipment information, $\rho=1$, and suppose
--   $$c_R>\psi_2=\frac{P_0m+2c_U/P_1}{P_0+2}.$$
--   Let $\psi_1=\frac{P_1m+c_U}{2P_1}$ and define the Table 2 prices: $w_E^I=(m+c_R)/2$, and $w_U^I=\psi_1$ if $c_R>\psi_1$ (case i-a), $w_U^I=c_R$ if $\psi_2<c_R\le\psi_1$ (case i-b).
--
--   Then:
--   1. the profile $\big(w_U^I,\ \max\{P_1w_U^I+P_0w_E^I,\,c_R\},\ w_E^I\big)$ is an equilibrium (a Pareto-undominated Nash equilibrium of the pricing game);
--   2. every equilibrium $(w_U,w_R,w_E)$ is one of contingent sourcing (the buyer orders only from U at Time 0 and, after a bad signal, from R at Time 1), with $w_U=w_U^I$, $w_E=(m+c_R)/2$, $w_R\ge P_1w_U+P_0w_E$, and $w_R=P_1w_U+P_0w_E$ when $c_R<\psi_1$.
--
--   In case (i-b) the maximum is just $P_1w_U^I+P_0w_E^I$. In case (i-a) Table 2 gives the interval $w_R\in[P_1w_U^I+P_0w_E^I,\,w_E^I]$, and the profile takes its lowest point that is admissible for supplier R ($w_R\ge c_R$).
--
--   **Formalization Note.** This replaces `proposition_2_i` and `proposition_2_i_corrected`, both disproved, with two changes. First, the equality clause for $w_R$ is required only for $c_R<\psi_1$: at $c_R=\psi_1$ the whole (i-a) interval gives equilibria. Second, the exhibited equilibrium uses $\max\{P_1w_U^I+P_0w_E^I,c_R\}$ instead of the bare lower end $P_1w_U^I+P_0w_E^I$. In case (i-a) that lower end can be below $c_R$, and so outside R's strategy space; for example $m=10$, $P_1=1/2$, $c_U=0$, $c_R=9$ gives $29/4<9$. "Contingent sourcing" is case i of the buyer's response, with footnote 11's tie-break. Parts (ii)–(iii) of Proposition 2 are not stated.
-- source:
--   Lu & Tomlin, Forewarned Is Forearmed?, SSRN 4260604 author manuscript (1 May 2023) of MSOM doi:10.1287/msom.2021.0540, p. 17 (PDF 17), Proposition 2(i) and Table 2 rows (i-a), (i-b); boundary c_R = ψ_1 and R-feasibility of the (i-a) lower end corrected

import Mathlib
import Definitions.Def_ContingentSourcing_Competition_Model

namespace ContingentSourcing.Competition

/-- Proposition 2(i), p. 17, with Table 2 (i-a)/(i-b), corrected: at ρ = 1 and c_R > ψ_2 the Table 2
profile with w_R raised to max(P_1 w_U + P_0 w_E, c_R) (the lower end of Table 2's (i-a) interval
intersected with R's strategy space) is an equilibrium, and every equilibrium is contingent sourcing
with w_U = w_U^I, w_E = (m + c_R)/2, w_R ≥ P_1 w_U + P_0 w_E, and w_R = P_1 w_U + P_0 w_E when c_R < ψ_1. -/
theorem proposition_2_i_corrected_v2 (P : Params) (hP : P.Standing) (h : P.psi2 < P.cR) :
    P.IsEquilibrium 1 ⟨P.priceI.wU, max P.priceI.wR P.cR, P.priceI.wE⟩ ∧ ∀ w, P.IsEquilibrium 1 w →
      P.Contingent 1 w ∧ w.wU = P.priceI.wU ∧ w.wE = (P.m + P.cR) / 2 ∧
      (P.psi1 ≤ P.cR → P.P1 * w.wU + P.P0 * w.wE ≤ w.wR) ∧
      (P.cR < P.psi1 → w.wR = P.P1 * w.wU + P.P0 * w.wE) := by sorry

end ContingentSourcing.Competition
