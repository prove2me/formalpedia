-- Prove2me | Theorems.Thm_CODATA_codata_self_consistent
-- name    : CODATA.codata_self_consistent
-- status  : Open
-- author  : @Lucas
-- created : 2026-10-21T01:40:43.128+00:00
-- url     : https://prove2.me/theorems/5262484f-86a5-45ef-9f12-4e646ce74b1b
-- title:
--   The 2022 adjustment is self-consistent
-- statement:
--   The goal theorem. Let L be a least-squares model of the main 2022
--   adjustment, 133 input data for 79 adjusted constants, and LG a model
--   of the separate adjustment of the sixteen values of the Newtonian
--   constant of gravitation, 16 input data for a single adjusted
--   constant. Suppose both weight matrices are symmetric and strictly
--   positive definite, the uncertainties of the sixteen values are
--   positive with unit self-correlations, and x and xg solve the
--   respective normal equations. Then: the degrees of freedom are 54 and
--   15; x and xg minimize their chi-square statistics; the Birge ratios
--   sqrt(44.2/54) and sqrt(12.9/15) round to the printed 0.90 and 0.93;
--   expanding the covariance matrix of the sixteen values of G by the
--   expansion factor 3.9 preserves every correlation coefficient; a single
--   rational relative-uncertainty witness reproduces the printed
--   uncertainties of the alpha family; and the exact derived constants
--   K_J, R_K, the flux quantum, the conductance quantum and its inverse,
--   F, R, the electronvolt and h in eV Hz^-1 agree with the printed digit
--   strings of Table XXXIII.
-- source:
--   P. J. Mohr, D. B. Newell, B. N. Taylor and E. Tiesinga, CODATA recommended values of the fundamental physical constants: 2022, J. Phys. Chem. Ref. Data 54, 033105 (2025), doi 10.1063/5.0279860; Rev. Mod. Phys. 97, 025002 (2025), doi 10.1103/RevModPhys.97.025002: section XII (the two adjustments, their degrees of freedom, chi-squares, Birge ratios and expansion factors) and Tables XXXII-XXXIII (the printed values and uncertainties).

import Mathlib
import Definitions.Def_CODATA_lsa
import Definitions.Def_CODATA_uncert
import Definitions.Def_CODATA_values

/-!
# The 2022 adjustment is self-consistent

The goal theorem of the mission packages the milestones into the
statement that the two adjustments of the 2022 CODATA report are
self-consistent. Let L be the main adjustment: 133 input data for 79
adjusted constants, hence 54 degrees of freedom. Let LG be the
separate adjustment of the sixteen values of the Newtonian constant of
gravitation: 16 input data for a single adjusted constant, hence 15
degrees of freedom. Suppose both weight matrices are symmetric and
strictly positive definite, the uncertainties of the sixteen values of
G are positive and their self-correlations are one, and x and xg
solve the respective normal equations. Then the degrees of freedom are
54 and 15; x and xg minimize their chi-square statistics; the Birge
ratios sqrt(44.2/54) and sqrt(12.9/15) round to the printed values
0.90 and 0.93; the expansion of the covariance matrix of the sixteen
values of G by the expansion factor 3.9 preserves every correlation
coefficient; a single rational relative-uncertainty witness
reproduces the printed two-significant-digit uncertainties of the
alpha family; and the exact derived constants K_J, R_K, Phi_0, G_0,
G_0⁻¹, F, R, the electronvolt and h in eV Hz⁻¹ agree with the printed
digit strings of Table XXXIII.

The mission source is P. J. Mohr, D. B. Newell, B. N. Taylor and
E. Tiesinga, CODATA recommended values of the fundamental physical
constants: 2022, J. Phys. Chem. Ref. Data 54, 033105 (2025), doi
10.1063/5.0279860, and the identical Rev. Mod. Phys. 97, 025002
(2025), doi 10.1103/RevModPhys.97.025002, section XII and Tables
XXXII-XXXIII.
-/

namespace CODATA

/-- The two adjustments of the 2022 CODATA report are self-consistent:
the main adjustment of 133 input data for 79 adjusted constants and
the separate adjustment of the sixteen values of the Newtonian
constant of gravitation have 54 and 15 degrees of freedom; solutions
of the normal equations minimize the chi-square statistic; the
resulting Birge ratios round to the printed 0.90 and 0.93; the
expansion factor 3.9 applied to the covariance matrix of the sixteen
values of G preserves every correlation; one rational
relative-uncertainty witness reproduces the printed uncertainties of
the alpha family; and the exact derived constants agree with their
printed digit strings. -/
theorem codata_self_consistent (L : LSQ 133 79) (LG : LSQ 16 1)
    (hG : IsSPD L.G) (hGg : IsSPD LG.G) (hu : ∀ i, 0 < LG.u i)
    (hur : ∀ i, LG.r i i = 1) (x : Fin 79 → ℝ) (hx : SolvesNormal L x)
    (xg : Fin 1 → ℝ) (hxg : SolvesNormal LG xg) :
    dof 133 79 = 54 ∧ dof 16 1 = 15 ∧
      Minimizes L x ∧ Minimizes LG xg ∧
      895/1000 ≤ Real.sqrt (442/10/54) ∧
        Real.sqrt (442/10/54) < 905/1000 ∧
      925/1000 ≤ Real.sqrt (129/10/15) ∧
        Real.sqrt (129/10/15) < 935/1000 ∧
      ∀ i j, corr (expandD (fun _ => 39/10) (covMat LG)) i j
        = corr (covMat LG) i j ∧
      (∃ ur : ℚ,
        155/(10:ℚ)^12 ≤ ur ∧ ur < 165/(10:ℚ)^12 ∧
        105/(10:ℚ)^14 ≤ ur * alphaVal ∧ ur * alphaVal < 115/(10:ℚ)^14 ∧
        205/(10:ℚ)^10 ≤ ur * alphaInvVal ∧
          ur * alphaInvVal < 215/(10:ℚ)^10 ∧
        195/(10:ℚ)^18 ≤ ur * mu0Val ∧ ur * mu0Val < 205/(10:ℚ)^18 ∧
        135/(10:ℚ)^23 ≤ ur * eps0Val ∧
          ur * eps0Val < 145/(10:ℚ)^23 ∧
        585/(10:ℚ)^10 ≤ ur * z0Val ∧ ur * z0Val < 595/(10:ℚ)^10) ∧
      4835978484/(10:ℚ)^4 ≤ kjVal/(10:ℚ)^9 ∧
        kjVal/(10:ℚ)^9 < 4835978485/(10:ℚ)^4 ∧
      2581280745/(10:ℚ)^5 ≤ rkVal ∧ rkVal < 2581280746/(10:ℚ)^5 ∧
      2067833848/(10:ℚ)^24 ≤ phi0Val ∧
        phi0Val < 2067833849/(10:ℚ)^24 ∧
      7748091729/(10:ℚ)^14 ≤ g0Val ∧
        g0Val < 7748091730/(10:ℚ)^14 ∧
      1290640372/(10:ℚ)^5 ≤ g0invVal ∧
        g0invVal < 1290640373/(10:ℚ)^5 ∧
      9648533212/(10:ℚ)^5 ≤ faradayVal ∧
        faradayVal < 9648533213/(10:ℚ)^5 ∧
      8314462618/(10:ℚ)^9 ≤ gasVal ∧ gasVal < 8314462619/(10:ℚ)^9 ∧
      eVoltVal = 1602176634/(10:ℚ)^28 ∧
      4135667696/(10:ℚ)^24 ≤ h_eV ∧
        h_eV < 4135667697/(10:ℚ)^24 := by
  sorry

end CODATA
