-- Prove2me | Theorems.Thm_DefectCoverUp_USEquilibrium_profit_difference
-- name    : DefectCoverUp.USEquilibrium.profit_difference
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-19T01:17:33.481148+00:00
-- url     : https://prove2.me/theorems/148b4398-8fcf-42de-949b-963fb2cea619
-- title:
--   Equations (15)–(16), p. 30 (PDF 31) — U.S. profit difference π_(R,I) − π_(NR) in closed form
-- statement:
--   Let $\pi_{R,I}^{US}$ be the manufacturer's expected profit after reporting when the regulator investigates immediately, and $\pi_{NR}^{US}$ her profit from concealing the signal. For admissible harm and reliability,
--
--   $$
--   \pi_{R,I}^{US}-\pi_{NR}^{US}=P(D\mid\widetilde D)\Omega_1(h)-\frac{plh}{\bar v},
--   $$
--
--   where $\Omega_1$ is the exact cubic of equation (16). This identity is the starting point for the manufacturer's reporting threshold.
--
--   **Formalization Note** Both profits are defined by the model's primitive payoffs and interval integrals, rather than by the displayed cubic.
-- source:
--   Cho, DeMiguel & Hwang, Cover-up of vehicle defects: the role of regulator investigation announcements, accepted manuscript (Management Science 67(6), 2021; LBS Research Online eprint 1396), proof of Proposition 2, Step 1, p. 30 (PDF 31), equations (15)–(16)

import Mathlib
import Definitions.Def_DefectCoverUp_USEquilibrium_Model

namespace DefectCoverUp.USEquilibrium

theorem profit_difference (P : Params) (hP : P.Standing)
    (h : ℝ) (hh : h ∈ Set.Ioc 0 P.hbar) (ρ : ℝ) (hρ : ρ ∈ Set.Icc (0 : ℝ) 1) :
    piRI P h ρ - piNR P h ρ =
      post P ρ * Omega1 P h - P.p * P.l * h / P.vbar := by sorry

end DefectCoverUp.USEquilibrium
