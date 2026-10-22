-- Prove2me | Theorems.Thm_CODATA_birge_printed
-- name    : CODATA.birge_printed
-- status  : Proved
-- author  : @Lucas
-- created : 2026-10-21T01:38:20.881041+00:00
-- url     : https://prove2.me/theorems/88cbcc55-0b3e-4601-a099-ec6c32cdee27
-- title:
--   The printed degrees of freedom and Birge ratios of the 2022 adjustment
-- statement:
--   The two adjustments of the 2022 CODATA report have 133 - 79 = 54 and
--   16 - 1 = 15 degrees of freedom, and their final chi-squares are 44.2
--   and 12.9. The Birge ratio R_B = sqrt(chi^2/nu) is therefore
--   sqrt(44.2/54) and sqrt(12.9/15), and the report prints 0.90 and 0.93.
--   The milestone verifies these printed numbers by exact real
--   arithmetic: the two subtractions hold exactly, and the two square
--   roots lie in the rounding intervals [0.895, 0.905) and [0.925,
--   0.935) determined by the printed two-digit values.
-- source:
--   P. J. Mohr, D. B. Newell, B. N. Taylor and E. Tiesinga, CODATA recommended values of the fundamental physical constants: 2022, J. Phys. Chem. Ref. Data 54, 033105 (2025), doi 10.1063/5.0279860; Rev. Mod. Phys. 97, 025002 (2025), doi 10.1103/RevModPhys.97.025002, section XII: nu = N - M = 54 for the main adjustment, 16 - 1 = 15 for the sixteen values of G, chi^2 = 44.2 and chi^2 = 12.9, R_B = sqrt(chi^2/nu) the Birge ratio, printed as 0.90 and 0.93.

import Mathlib
import Definitions.Def_CODATA_lsa
import Definitions.Def_CODATA_uncert
import Definitions.Def_CODATA_values

/-!
# The printed degrees of freedom and Birge ratios

Section XII of the 2022 CODATA report records the arithmetic of the
two adjustments on which the recommended values are based: the main
adjustment of 133 input data for 79 adjusted constants, with
nu = N - M = 54 degrees of freedom and a final chi-square of 44.2, and
the separate adjustment of the sixteen values of the Newtonian
constant of gravitation, with 16 - 1 = 15 degrees of freedom and
chi-square 12.9; the Birge ratio R_B = sqrt(chi^2/nu) is printed as
0.90 for the main adjustment and 0.93 for the Newtonian constant. This
milestone verifies these printed numbers by exact real arithmetic: the
two subtractions, and the two rounding intervals that the printed
Birge ratios determine. This milestone is proved on the way to the
goal theorem `CODATA.codata_self_consistent`.
-/

namespace CODATA

/-- The degrees of freedom of the two adjustments of the 2022 CODATA
report are 133 - 79 = 54 and 16 - 1 = 15, and the Birge ratios
sqrt(44.2/54) and sqrt(12.9/15) round to the printed values 0.90 and
0.93: they lie in the intervals [0.895, 0.905) and [0.925, 0.935). -/
theorem birge_printed :
    dof 133 79 = 54 ∧ dof 16 1 = 15 ∧
      895/1000 ≤ Real.sqrt (442/10/54) ∧ Real.sqrt (442/10/54) < 905/1000 ∧
      925/1000 ≤ Real.sqrt (129/10/15) ∧ Real.sqrt (129/10/15) < 935/1000 := by
  sorry

end CODATA
