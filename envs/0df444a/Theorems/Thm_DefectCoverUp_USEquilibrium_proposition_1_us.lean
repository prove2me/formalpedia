-- Prove2me | Theorems.Thm_DefectCoverUp_USEquilibrium_proposition_1_us
-- name    : DefectCoverUp.USEquilibrium.proposition_1_us
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-19T01:17:43.800494+00:00
-- url     : https://prove2.me/theorems/2ad8dbbb-418a-47a8-b4fe-6e18a5376448
-- title:
--   Proposition 1 (U.S. case), p. 13 (PDF 14) — the regulator investigates a report iff h ≥ h_I^US and ρ ≥ ρ_I^US(h)
-- statement:
--   Suppose the manufacturer reports a potential defect. Under the U.S. announcement policy there are a harm threshold $h_I^{US}\in(0,\bar h)$ and a reliability threshold curve $\rho_I^{US}:[h_I^{US},\bar h]\to[0,1]$ with $\rho_I^{US}(h_I^{US})=1$ such that
--
--   $$
--   \text{the regulator investigates immediately}\quad\Longleftrightarrow\quad h\ge h_I^{US}\text{ and }\rho\ge\rho_I^{US}(h).
--   $$
--
--   This combines the two U.S. clauses of Proposition 1 and supplies the regulator's continuation action in the equilibrium theorem.
--
--   **Formalization Note** The U.K. clauses of the printed proposition are outside this mission. The curve is represented as a total real function, constrained on its stated domain.
-- source:
--   Cho, DeMiguel & Hwang, Cover-up of vehicle defects: the role of regulator investigation announcements, accepted manuscript (Management Science 67(6), 2021; LBS Research Online eprint 1396), Proposition 1, U.S. case, p. 13 (PDF 14)

import Mathlib
import Definitions.Def_DefectCoverUp_USEquilibrium_Model

namespace DefectCoverUp.USEquilibrium

theorem proposition_1_us (P : Params) (hP : P.Standing) :
    ∃ hI ∈ Set.Ioo 0 P.hbar, ∃ ρI : ℝ → ℝ,
      ρI hI = 1 ∧
      (∀ h ∈ Set.Icc hI P.hbar, ρI h ∈ Set.Icc (0 : ℝ) 1) ∧
      ∀ h ∈ Set.Ioc 0 P.hbar, ∀ ρ ∈ Set.Icc (0 : ℝ) 1,
        (investigates P h ρ ↔ hI ≤ h ∧ ρI h ≤ ρ) := by sorry

end DefectCoverUp.USEquilibrium
