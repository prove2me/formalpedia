-- Prove2me | Theorems.Thm_DefectCoverUp_USEquilibrium_manufacturer_report_rule
-- name    : DefectCoverUp.USEquilibrium.manufacturer_report_rule
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-19T01:17:46.186871+00:00
-- url     : https://prove2.me/theorems/c9c9a530-30be-4d0b-b68e-8bd480f7bf39
-- title:
--   Proof of Proposition 2, Step 1, p. 30 (PDF 31) — against immediate investigation, report iff h ≥ h_R^US and ρ ≥ ρ_R^US(h)
-- statement:
--   If the regulator would investigate immediately after a report, there are a harm threshold $h_R^{US}\in(0,\bar h)$ and a curve $\rho_R^{US}:[h_R^{US},\bar h]\to[0,1]$ satisfying $\rho_R^{US}(h_R^{US})=1$ and
--
--   $$
--   \pi_{R,I}^{US}\ge\pi_{NR}^{US}\quad\Longleftrightarrow\quad h\ge h_R^{US}\text{ and }\rho\ge\rho_R^{US}(h),\qquad
--   \rho_R^{US}(h)=\max\{\rho_1(h),0\},
--   $$
--
--   where $\rho_1(h)$ is the fraction in equation (17). This determines when reporting is optimal against an immediate investigation.
--
--   **Formalization Note** The formula and range condition for the curve are imposed only where $h\ge h_R^{US}$; outside that range the fraction need not be in $[0,1]$.
-- source:
--   Cho, DeMiguel & Hwang, Cover-up of vehicle defects: the role of regulator investigation announcements, accepted manuscript (Management Science 67(6), 2021; LBS Research Online eprint 1396), proof of Proposition 2, Step 1, p. 30 (PDF 31), equation (17) and final paragraph

import Mathlib
import Definitions.Def_DefectCoverUp_USEquilibrium_Model

namespace DefectCoverUp.USEquilibrium

theorem manufacturer_report_rule (P : Params) (hP : P.Standing) :
    ∃ hR ∈ Set.Ioo 0 P.hbar, ∃ ρR : ℝ → ℝ,
      ρR hR = 1 ∧
      (∀ h ∈ Set.Icc hR P.hbar, ρR h ∈ Set.Icc (0 : ℝ) 1) ∧
      (∀ h ∈ Set.Icc hR P.hbar, ρR h = max (rho1 P h) 0) ∧
      ∀ h ∈ Set.Ioc 0 P.hbar, ∀ ρ ∈ Set.Icc (0 : ℝ) 1,
        (piNR P h ρ ≤ piRI P h ρ ↔ hR ≤ h ∧ ρR h ≤ ρ) := by sorry

end DefectCoverUp.USEquilibrium
