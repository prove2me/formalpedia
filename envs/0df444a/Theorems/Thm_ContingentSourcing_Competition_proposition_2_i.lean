-- Prove2me | Theorems.Thm_ContingentSourcing_Competition_proposition_2_i
-- name    : ContingentSourcing.Competition.proposition_2_i
-- status  : Disproved
-- author  : @mikedeng1
-- created : 2026-10-22T17:31:08.051826+00:00
-- url     : https://prove2.me/theorems/c2f054ea-dfd6-482b-a572-80c2b1c3c6ab
-- title:
--   Proposition 2(i), p. 17 — with perfect shipment information and c_R > ψ_2, the buyer sources only from U at Time 0 and from R after a bad signal; Table 2 (i-a)/(i-b)
-- statement:
--   Take perfect shipment information, $\rho=1$, and suppose
--   $$c_R>\psi_2=\frac{P_0m+2c_U/P_1}{P_0+2}.$$
--   Let $\psi_1=\frac{P_1m+c_U}{2P_1}$ and define the Table 2 prices: $w_E^I=(m+c_R)/2$, and $w_U^I=\psi_1$ if $c_R>\psi_1$ (case i-a), $w_U^I=c_R$ if $\psi_2<c_R\le\psi_1$ (case i-b).
--
--   Then:
--   1. the profile $(w_U^I,\ P_1w_U^I+P_0w_E^I,\ w_E^I)$ is an equilibrium (a Pareto-dominant Nash equilibrium of the pricing game);
--   2. every equilibrium $(w_U,w_R,w_E)$ is one of contingent sourcing (the buyer orders only from U at Time 0 and, after a bad signal, from R at Time 1), with $w_U=w_U^I$, $w_E=(m+c_R)/2$, and
--      - in case (i-a), $w_R\ge P_1w_U^I+P_0w_E^I$ (so $w_R\in[P_1w_U^I+P_0w_E^I,w_E^I]$);
--      - in case (i-b), $w_R=P_1w_U^I+P_0w_E^I$.
--
--   This is the perfect-information half of the comparison in Proposition 4.
--
--   **Formalization Note.** "Contingent sourcing" is case i of the buyer's response, with footnote 11's tie-break (the buyer sources contingently when indifferent); without it the (i-b) limit price is never a best response. Parts (ii)–(iii) of Proposition 2 are not stated: part (ii) is false as printed (at $m=10$, $P_1=1/2$, $c_U=0$, $c_R=3/2$ a contingent-sourcing profile is an undominated equilibrium).
-- source:
--   Lu & Tomlin, Forewarned Is Forearmed?, SSRN 4260604 author manuscript (1 May 2023) of MSOM doi:10.1287/msom.2021.0540, p. 17 (PDF 17), Proposition 2(i) and Table 2 rows (i-a), (i-b)

import Mathlib
import Definitions.Def_ContingentSourcing_Competition_Model

namespace ContingentSourcing.Competition

/-- Proposition 2(i), p. 17, with Table 2 (i-a)/(i-b): at ρ = 1 and c_R > ψ_2 the Table 2 profile is
an equilibrium, and every equilibrium is contingent sourcing with w_U = w_U^I, w_E = (m + c_R)/2 and
w_R in Table 2's set. -/
theorem proposition_2_i (P : Params) (hP : P.Standing) (h : P.psi2 < P.cR) :
    P.IsEquilibrium 1 P.priceI ∧ ∀ w, P.IsEquilibrium 1 w →
      P.Contingent 1 w ∧ w.wU = P.priceI.wU ∧ w.wE = (P.m + P.cR) / 2 ∧
      (P.psi1 < P.cR → P.P1 * w.wU + P.P0 * w.wE ≤ w.wR) ∧
      (P.cR ≤ P.psi1 → w.wR = P.P1 * w.wU + P.P0 * w.wE) := by sorry

end ContingentSourcing.Competition
