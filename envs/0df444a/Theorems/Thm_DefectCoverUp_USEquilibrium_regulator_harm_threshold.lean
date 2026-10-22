-- Prove2me | Theorems.Thm_DefectCoverUp_USEquilibrium_regulator_harm_threshold
-- name    : DefectCoverUp.USEquilibrium.regulator_harm_threshold
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-19T01:17:38.817259+00:00
-- url     : https://prove2.me/theorems/b4ef8ddf-14cd-4dcd-b293-7ab43e89608e
-- title:
--   Proof of Proposition 1 (U.S.), p. 28 (PDF 29) — the cubic χ̂1 gives the regulator's harm threshold h_I^US
-- statement:
--   The function $\widehat\chi_1(h)=\chi_1(h)-lh(\bar v-h/2)/\bar v-C$ is cubic with negative leading coefficient $-3l/(2\bar h\bar v)$. Its endpoint values are
--
--   $$
--   \widehat\chi_1(0)=-\frac{rl}{\bar v}(\bar v-p)-C<0,\qquad
--   \widehat\chi_1(\bar h)=\frac{r+\bar h}{2\bar v}(\bar v-p)(1-l)>0.
--   $$
--
--   There is $h_I^{US}\in(0,\bar h)$ such that $\widehat\chi_1(h)\ge0$ exactly when $h\ge h_I^{US}$ on $[0,\bar h]$. Below that threshold, immediate investigation has lower welfare for every reliability $\rho$. At or above it, immediate investigation has at least as much welfare exactly when $\rho\ge\rho_I^{US}(h)$, where $\rho_I^{US}(h)=\max\{\rho'(h),0\}\in[0,1]$ and $\rho'$ is given by equation (11).
--
--   This is the harm and reliability comparison in the U.S. case of the proof of Proposition 1.
-- source:
--   Cho, DeMiguel & Hwang, Cover-up of vehicle defects: the role of regulator investigation announcements, accepted manuscript (Management Science 67(6), 2021; LBS Research Online eprint 1396), proof of Proposition 1, U.S. case, p. 28 (PDF 29), paragraph after equation (11)

import Mathlib
import Definitions.Def_DefectCoverUp_USEquilibrium_Model

namespace DefectCoverUp.USEquilibrium

theorem regulator_harm_threshold (P : Params) (hP : P.Standing) :
    (∃ a b c : ℝ, ∀ h : ℝ,
      chi1hat P h = -3 * P.l / (2 * P.hbar * P.vbar) * h ^ 3 +
        a * h ^ 2 + b * h + c) ∧
    -3 * P.l / (2 * P.hbar * P.vbar) < 0 ∧
    chi1hat P 0 = -P.r * P.l / P.vbar * (P.vbar - P.p) - P.C ∧
    chi1hat P 0 < 0 ∧
    chi1hat P P.hbar =
      (P.r + P.hbar) / (2 * P.vbar) * (P.vbar - P.p) * (1 - P.l) ∧
    0 < chi1hat P P.hbar ∧
    ∃ hI ∈ Set.Ioo 0 P.hbar, ∃ ρI : ℝ → ℝ,
      (∀ h ∈ Set.Icc (0 : ℝ) P.hbar, (0 ≤ chi1hat P h ↔ hI ≤ h)) ∧
      (∀ h ∈ Set.Icc hI P.hbar,
        ρI h = max (rhoPrime P h) 0 ∧ ρI h ∈ Set.Icc (0 : ℝ) 1) ∧
      (∀ h ∈ Set.Ioc 0 P.hbar,
        ((∀ ρ ∈ Set.Icc (0 : ℝ) 1, WRI P h ρ - WRNI P h ρ < 0) ↔ h < hI)) ∧
      ∀ h ∈ Set.Ioc 0 P.hbar, ∀ ρ ∈ Set.Icc (0 : ℝ) 1,
        (0 ≤ WRI P h ρ - WRNI P h ρ ↔ hI ≤ h ∧ ρI h ≤ ρ) := by sorry

end DefectCoverUp.USEquilibrium
