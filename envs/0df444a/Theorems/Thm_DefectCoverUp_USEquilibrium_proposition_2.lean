-- Prove2me | Theorems.Thm_DefectCoverUp_USEquilibrium_proposition_2
-- name    : DefectCoverUp.USEquilibrium.proposition_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-19T01:17:38.879655+00:00
-- url     : https://prove2.me/theorems/f69d8a59-747b-4b62-8dd7-5bb642eb7f4a
-- title:
--   Proposition 2, p. 15 (PDF 16) — in the U.S., thresholds h_R^US, ρ_R^US(h) with Proposition 1's h_I^US, ρ_I^US determine the unique SPNE
-- statement:
--   For the U.S. investigation-announcement policy, let $(R,I)$ mean reporting followed by immediate investigation, $(R,NI)$ reporting without immediate investigation, and $(NR,I)$ no report with investigation as the regulator's off-path response to a report. There exist fixed thresholds $h_I^{US},h_R^{US}\in(0,\bar h)$ and curves $\rho_I^{US},\rho_R^{US}$, each mapping its threshold-to-$\bar h$ interval into $[0,1]$ and equal to one at its harm threshold. The regulator curve obeys Proposition 1. For every admissible $h$ and $\rho$, the unique subgame perfect equilibrium is:
--
--   $$
--   \begin{cases}
--   (R,I),&h\ge\max\{h_I^{US},h_R^{US}\},\;\rho\ge\max\{\rho_I^{US}(h),\rho_R^{US}(h)\},\\
--   (R,NI),&h<h_I^{US}\text{ or }(h\ge h_I^{US},\rho<\rho_I^{US}(h)),\\
--   (NR,I),&(h_I^{US}\le h<h_R^{US},\rho\ge\rho_I^{US}(h))\text{ or }(h\ge h_R^{US},\rho_I^{US}(h)\le\rho<\rho_R^{US}(h)).
--   \end{cases}
--   $$
--
--   When the manufacturer does not report, the regulator takes no immediate action on the realized path. The last region captures cover-up even for substantial harm when signal reliability is intermediate.
--
--   **Formalization Note** The strategy profile records the regulator's response to a hypothetical report, so $(NR,I)$ has no immediate investigation on the realized path. Both tie breaks are built into the equilibrium predicate. The condition $0<P_D<1$ is added to the paper's standing assumptions for its reliability normalization.
-- source:
--   Cho, DeMiguel & Hwang, Cover-up of vehicle defects: the role of regulator investigation announcements, accepted manuscript (Management Science 67(6), 2021; LBS Research Online eprint 1396), Proposition 2, p. 15 (PDF 16), with proof Step 2, pp. 30–31 (PDF 31–32)

import Mathlib
import Definitions.Def_DefectCoverUp_USEquilibrium_Model

namespace DefectCoverUp.USEquilibrium

theorem proposition_2 (P : Params) (hP : P.Standing) :
    ∃ hI ∈ Set.Ioo 0 P.hbar, ∃ ρI : ℝ → ℝ,
      ∃ hR ∈ Set.Ioo 0 P.hbar, ∃ ρR : ℝ → ℝ,
        ρI hI = 1 ∧
        (∀ h ∈ Set.Icc hI P.hbar, ρI h ∈ Set.Icc (0 : ℝ) 1) ∧
        ρR hR = 1 ∧
        (∀ h ∈ Set.Icc hR P.hbar, ρR h ∈ Set.Icc (0 : ℝ) 1) ∧
        (∀ h ∈ Set.Ioc 0 P.hbar, ∀ ρ ∈ Set.Icc (0 : ℝ) 1,
          (investigates P h ρ ↔ hI ≤ h ∧ ρI h ≤ ρ)) ∧
        ∀ h ∈ Set.Ioc 0 P.hbar, ∀ ρ ∈ Set.Icc (0 : ℝ) 1,
          ((max hI hR ≤ h ∧ max (ρI h) (ρR h) ≤ ρ) →
            ∀ σ : MAct × RAct, IsSPNE P h ρ σ ↔ σ = (MAct.R, RAct.I)) ∧
          ((h < hI ∨ (hI ≤ h ∧ ρ < ρI h)) →
            ∀ σ : MAct × RAct, IsSPNE P h ρ σ ↔ σ = (MAct.R, RAct.NI)) ∧
          (((hI ≤ h ∧ h < hR ∧ ρI h ≤ ρ) ∨
            (hR ≤ h ∧ ρI h ≤ ρ ∧ ρ < ρR h)) →
            ∀ σ : MAct × RAct, IsSPNE P h ρ σ ↔ σ = (MAct.NR, RAct.I)) := by sorry

end DefectCoverUp.USEquilibrium
