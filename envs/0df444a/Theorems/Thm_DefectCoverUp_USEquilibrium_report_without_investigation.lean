-- Prove2me | Theorems.Thm_DefectCoverUp_USEquilibrium_report_without_investigation
-- name    : DefectCoverUp.USEquilibrium.report_without_investigation
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-19T01:17:33.775703+00:00
-- url     : https://prove2.me/theorems/2838b392-8dc9-472f-ae66-f1c4c7dee39b
-- title:
--   Proof of Proposition 2, Step 2, p. 31 (PDF 32) — by (5), π_(R,NI) ≥ π_(NR)
-- statement:
--   If a report will not trigger an immediate investigation, the manufacturer's expected U.S. profit from reporting is at least her profit from concealing the signal. For admissible $h$ and $\rho$,
--
--   $$
--   \pi_{R,NI}^{US}(h,\rho)\ge\pi_{NR}^{US}(h,\rho).
--   $$
--
--   The inequality is the profit comparison used for the report-without-investigation equilibrium region; the penalty on a discovered cover-up makes it weak.
--
--   **Formalization Note** The penalty parameters and discovery probability are nonnegative in the standing conditions.
-- source:
--   Cho, DeMiguel & Hwang, Cover-up of vehicle defects: the role of regulator investigation announcements, accepted manuscript (Management Science 67(6), 2021; LBS Research Online eprint 1396), proof of Proposition 2, Step 2, p. 31 (PDF 32), paragraph beginning “First, suppose” and equation (5), p. 11 (PDF 12)

import Mathlib
import Definitions.Def_DefectCoverUp_USEquilibrium_Model

namespace DefectCoverUp.USEquilibrium

theorem report_without_investigation (P : Params) (hP : P.Standing)
    (h : ℝ) (hh : h ∈ Set.Ioc 0 P.hbar) (ρ : ℝ) (hρ : ρ ∈ Set.Icc (0 : ℝ) 1) :
    piNR P h ρ ≤ piRNI P h ρ := by sorry

end DefectCoverUp.USEquilibrium
