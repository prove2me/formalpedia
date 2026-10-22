-- Prove2me | Theorems.Thm_DefectCoverUp_USEquilibrium_manufacturer_harm_threshold
-- name    : DefectCoverUp.USEquilibrium.manufacturer_harm_threshold
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-19T01:17:38.396839+00:00
-- url     : https://prove2.me/theorems/7956f210-f922-40a2-b122-042fa9c1a5ad
-- title:
--   Proof of Proposition 2, Step 1, p. 30 (PDF 31) — the cubic Ω̂1, equation (18), and the harm threshold h_R^US
-- statement:
--   The function $\widehat\Omega_1(h)=\Omega_1(h)-plh/\bar v$ is cubic with negative leading coefficient $-l/(\bar h\bar v)$. Its value at zero is negative:
--
--   $$
--   \widehat\Omega_1(0)=-lr\left(1-\frac p{\bar v}\right)<0.
--   $$
--
--   At maximum harm, equation (18) gives
--
--   $$
--   \widehat\Omega_1(\bar h)=\frac{(1-l)(\bar v-p)r+2K_2\theta\bar v+\bar h((1-l)(\bar v-p)+2K_1\theta\bar v)}{2\bar v}>0.
--   $$
--
--   There is $h_R^{US}\in(0,\bar h)$ such that $\widehat\Omega_1(h)\ge0$ exactly when $h\ge h_R^{US}$ on $[0,\bar h]$. This locates the manufacturer's harm cutoff before the reliability comparison.
-- source:
--   Cho, DeMiguel & Hwang, Cover-up of vehicle defects: the role of regulator investigation announcements, accepted manuscript (Management Science 67(6), 2021; LBS Research Online eprint 1396), proof of Proposition 2, Step 1, p. 30 (PDF 31), equation (18) and following sentence

import Mathlib
import Definitions.Def_DefectCoverUp_USEquilibrium_Model

namespace DefectCoverUp.USEquilibrium

theorem manufacturer_harm_threshold (P : Params) (hP : P.Standing) :
    (∃ a b c : ℝ, ∀ h : ℝ,
      Omega1hat P h = -P.l / (P.hbar * P.vbar) * h ^ 3 +
        a * h ^ 2 + b * h + c) ∧
    -P.l / (P.hbar * P.vbar) < 0 ∧
    Omega1hat P 0 = -P.l * P.r * (1 - P.p / P.vbar) ∧
    Omega1hat P 0 < 0 ∧
    Omega1hat P P.hbar =
      (1 / (2 * P.vbar)) *
        ((1 - P.l) * (P.vbar - P.p) * P.r + 2 * P.K2 * P.th * P.vbar +
          P.hbar * ((1 - P.l) * (P.vbar - P.p) + 2 * P.K1 * P.th * P.vbar)) ∧
    0 < Omega1hat P P.hbar ∧
    ∃ hR ∈ Set.Ioo 0 P.hbar,
      ∀ h ∈ Set.Icc (0 : ℝ) P.hbar, (0 ≤ Omega1hat P h ↔ hR ≤ h) := by sorry

end DefectCoverUp.USEquilibrium
