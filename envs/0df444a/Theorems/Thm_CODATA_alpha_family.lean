-- Prove2me | Theorems.Thm_CODATA_alpha_family
-- name    : CODATA.alpha_family
-- status  : Open
-- author  : @Lucas
-- created : 2026-10-21T01:40:06.799475+00:00
-- url     : https://prove2.me/theorems/096321b4-3254-457c-bd3e-606f4210391b
-- title:
--   A single relative-uncertainty witness for the alpha family
-- statement:
--   In the 2022 CODATA adjustment the fine-structure constant alpha, its
--   inverse, the vacuum magnetic permeability mu_0, the vacuum electric
--   permittivity eps_0 and the impedance of vacuum Z_0 form a family
--   determined by alpha, all other factors being exact. Their printed
--   uncertainties in Table XXXIII carry two significant digits: alpha =
--   7.297 352 5643(11) x 10^-3, 1/alpha = 137.035 999 177(21), mu_0 =
--   1.256 637 061 27(20) x 10^-6, eps_0 = 8.854 187 8188(14) x 10^-12,
--   Z_0 = 376.730 313 412(58). The milestone verifies the joint
--   consistency of these five printed uncertainty statements: there is a
--   single rational relative uncertainty ur, of order 1.6 x 10^-10, such
--   that ur times each of the five rational values lies in the rounding
--   interval determined by the printed two-digit uncertainty.
-- source:
--   P. J. Mohr, D. B. Newell, B. N. Taylor and E. Tiesinga, CODATA recommended values of the fundamental physical constants: 2022, J. Phys. Chem. Ref. Data 54, 033105 (2025), doi 10.1063/5.0279860; Rev. Mod. Phys. 97, 025002 (2025), doi 10.1103/RevModPhys.97.025002, Table XXXIII: the printed values and two-significant-digit uncertainties of alpha, 1/alpha, mu_0, eps_0 and Z_0, whose recommended values are mutually determined through the exact constants.

import Mathlib
import Definitions.Def_CODATA_lsa
import Definitions.Def_CODATA_uncert
import Definitions.Def_CODATA_values

/-!
# A single relative-uncertainty witness for the alpha family

In the 2022 CODATA adjustment the vacuum magnetic permeability, the
vacuum electric permittivity, the impedance of vacuum and the two
fine-structure-constant entries form a family: mu_0 = 2 alpha h/(e² c),
eps_0, Z_0 and alpha are mutually determined, the other factors being
exact. Their printed uncertainties in Table XXXIII (two significant
digits) are therefore all products of a single relative uncertainty
with the respective exact values: alpha = 7.297 352 5643(11) × 10⁻³,
1/alpha = 137.035 999 177(21), mu_0 = 1.256 637 061 27(20) × 10⁻⁶,
eps_0 = 8.854 187 8188(14) × 10⁻¹², Z_0 = 376.730 313 412(58). This
milestone verifies the consistency of these five printed uncertainty
statements by exact rational arithmetic: there is a single rational
relative-uncertainty witness ur, of order 1.6 × 10⁻¹⁰, such that ur
times each of the five rational values lies in the rounding interval
determined by the printed two-digit uncertainty. This milestone is
proved on the way to the goal theorem
`CODATA.codata_self_consistent`.
-/

namespace CODATA

/-- There is a single rational relative uncertainty ur with
1.55 × 10⁻¹⁰ ≤ ur < 1.65 × 10⁻¹⁰ such that ur alpha lies in
[1.05, 1.15) × 10⁻¹², ur/alpha lies in [2.05, 2.15) × 10⁻⁸,
ur mu_0 lies in [1.95, 2.05) × 10⁻¹⁶, ur eps_0 lies in
[1.35, 1.45) × 10⁻²¹ and ur Z_0 lies in [5.85, 5.95) × 10⁻⁸: one
witness reproduces the printed two-significant-digit uncertainties of
the whole alpha family of the 2022 adjustment. -/
theorem alpha_family :
    ∃ ur : ℚ,
      155/(10:ℚ)^12 ≤ ur ∧ ur < 165/(10:ℚ)^12 ∧
      105/(10:ℚ)^14 ≤ ur * alphaVal ∧ ur * alphaVal < 115/(10:ℚ)^14 ∧
      205/(10:ℚ)^10 ≤ ur * alphaInvVal ∧
      ur * alphaInvVal < 215/(10:ℚ)^10 ∧
      195/(10:ℚ)^18 ≤ ur * mu0Val ∧ ur * mu0Val < 205/(10:ℚ)^18 ∧
      135/(10:ℚ)^23 ≤ ur * eps0Val ∧ ur * eps0Val < 145/(10:ℚ)^23 ∧
      585/(10:ℚ)^10 ≤ ur * z0Val ∧ ur * z0Val < 595/(10:ℚ)^10 := by
  sorry

end CODATA
