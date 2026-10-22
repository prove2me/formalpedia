-- Prove2me | Theorems.Thm_DefectCoverUp_USEquilibrium_welfare_difference
-- name    : DefectCoverUp.USEquilibrium.welfare_difference
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-19T01:17:25.716981+00:00
-- url     : https://prove2.me/theorems/e6a66f0e-81a0-41ba-aacd-7b8f243bca06
-- title:
--   Equations (9)–(10), p. 28 (PDF 29) — U.S. welfare difference W_(R,I) − W_(R,NI) in closed form
-- statement:
--   For the U.S. policy, let $W_{R,I}^{US}$ and $W_{R,NI}^{US}$ be the regulator's expected welfare after a report with and without an immediate investigation. For admissible harm $h$ and reliability $\rho$, the integral model gives
--
--   $$
--   W_{R,I}^{US}-W_{R,NI}^{US}=P(D\mid\widetilde D)\chi_1(h)-\frac{lh}{\bar v}\left(\bar v-\frac h2\right)-C,
--   $$
--
--   where $\chi_1$ is exactly the polynomial displayed in equation (10). This identity relates the regulator's welfare comparison to the paper's harm threshold.
--
--   **Formalization Note** The theorem uses the shared standing conditions and $h\in(0,\bar h]$, $\rho\in[0,1]$.
-- source:
--   Cho, DeMiguel & Hwang, Cover-up of vehicle defects: the role of regulator investigation announcements, accepted manuscript (Management Science 67(6), 2021; LBS Research Online eprint 1396), proof of Proposition 1, U.S. case, p. 28 (PDF 29), equations (9)–(10)

import Mathlib
import Definitions.Def_DefectCoverUp_USEquilibrium_Model

namespace DefectCoverUp.USEquilibrium

theorem welfare_difference (P : Params) (hP : P.Standing)
    (h : ℝ) (hh : h ∈ Set.Ioc 0 P.hbar) (ρ : ℝ) (hρ : ρ ∈ Set.Icc (0 : ℝ) 1) :
    WRI P h ρ - WRNI P h ρ =
      post P ρ * chi1 P h - P.l * h / P.vbar * (P.vbar - h / 2) - P.C := by sorry

end DefectCoverUp.USEquilibrium
