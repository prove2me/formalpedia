-- Prove2me | solution 1 for fermatLastTheoremSeven
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:14.293936+00:00
-- url     : https://prove2.me/submissions/4ded82ef-590f-5840-9ca9-67ee01e903d1

import Theorems.Thm_flt_regular
import Theorems.Thm_IsCyclotomicExtension_Rat_seven_pid
import Mathlib.NumberTheory.NumberField.ClassNumber
import Mathlib.NumberTheory.Cyclotomic.Basic
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_fermatLastTheoremSeven

open NumberField

set_option backward.isDefEq.respectTransparency false in
theorem solution : FermatLastTheoremFor 7 := by
  haveI : Fact (Nat.Prime 7) := ⟨by norm_num⟩
  refine flt_regular (p := 7) ?_ (by norm_num)
  convert Nat.coprime_one_right _
  exact classNumber_eq_one_iff.2 (IsCyclotomicExtension.Rat.seven_pid (CyclotomicField 7 ℚ))

end S_fermatLastTheoremSeven
end P2MW
export P2MW.S_fermatLastTheoremSeven (solution)
