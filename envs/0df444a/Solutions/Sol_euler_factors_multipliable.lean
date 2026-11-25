-- Prove2me | solution 1 for euler_factors_multipliable
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T16:12:02.090658+00:00
-- url     : https://prove2.me/submissions/4215184e-c2ba-41ca-af6e-d65cf80e795c

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_CMEulerProducts_StepRegroup
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_CMEulerProducts_EulerFactorsMultipliable
import Theorems.Thm_CMEul_Mult_summable_norm_rpow
import Theorems.Thm_CMEul_Mult_abs_eulerFac_sub_one_le

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField
noncomputable section
theorem _root_.solution : CMEul.StepMult := by
  intro K _ _ _ M hM
  have hs : Summable (fun P : {P : Ideal (𝓞 K) // P.IsMaximal} => Formalism.HermitianLatticesTheory.eulerFac K M P.1 - 1) := by
    refine Summable.of_norm_bounded
      ((CMEul.Mult.summable_norm_rpow (K := K) (s := 3 / 2) (by norm_num)).mul_left 2) ?_
    intro P
    rw [Real.norm_eq_abs]
    exact CMEul.Mult.abs_eulerFac_sub_one_le M hM P.1 P.2
  simpa using Real.multipliable_one_add_of_summable hs
