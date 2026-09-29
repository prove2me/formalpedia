-- Prove2me | solution 1 for fermatLastTheoremEleven
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:14.293936+00:00
-- url     : https://prove2.me/submissions/c418e618-9e08-54f8-ba7c-22d2e3923e53

import Theorems.Thm_flt_regular
import Theorems.Thm_IsCyclotomicExtension_Rat_eleven_pid
import Mathlib.NumberTheory.NumberField.ClassNumber
import Mathlib.NumberTheory.Cyclotomic.Basic
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_fermatLastTheoremEleven

open NumberField

set_option backward.isDefEq.respectTransparency false in
theorem solution : FermatLastTheoremFor 11 := by
  haveI : Fact (Nat.Prime 11) := ⟨by norm_num⟩
  refine flt_regular (p := 11) ?_ (by norm_num)
  convert Nat.coprime_one_right _
  exact classNumber_eq_one_iff.2 (IsCyclotomicExtension.Rat.eleven_pid (CyclotomicField 11 ℚ))

end S_fermatLastTheoremEleven
end P2MW
export P2MW.S_fermatLastTheoremEleven (solution)
