-- Prove2me | Theorems.Thm_AvramDividend_Classical_valueFunctionLe_above_cap_of_nonempty
-- name    : AvramDividend.Classical.valueFunctionLe_above_cap_of_nonempty
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-04T18:08:59.970009+00:00
-- url     : https://prove2.me/theorems/c4e3f2b8-8dbe-4108-be46-efbdcb7259af
-- title:
--   Value above a dividend reserve cap with a nonempty strategy class
-- statement:
--   If the class of admissible strategies starting at reserve c with reserve cap c is nonempty, then starting with x>c pays an immediate lump sum x-c and afterwards has the same optimal capped value as starting at c. The result follows by two already Proved transformations of admissible strategies and value, and by supremum algebra with the nonemptiness condition explicit.
-- source:
--   Avram classical dividend mission; helper using the Proved add_initial_excess_admissible_value and strip_initial_excess_admissible_value transformations, source SHA-256 15d38a95b9166e2c968f1857033c0695aeadb8937ec42cdb3c7591249fc4312f

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_add_initial_excess_admissible_value
import Theorems.Thm_AvramDividend_Classical_strip_initial_excess_admissible_value

open MeasureTheory Filter Set Topology
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.valueFunctionLe_above_cap_of_nonempty {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (q x c : ℝ)
    (hc : 0 ≤ c) (hcx : c < x)
    (hne : ∃ E : ℝ≥0 → Ω → ℝ,
      IsAdmissibleLe X c (ENNReal.ofReal c) E) :
    valueFunctionLe X q (ENNReal.ofReal c) x =
      ENNReal.ofReal (x - c) + valueFunctionLe X q (ENNReal.ofReal c) c := by
  sorry
