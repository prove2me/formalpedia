-- Prove2me | Theorems.Thm_Formalism_GM_DimensionMonotonicity_ycond_glAct_le
-- name    : Formalism.GM.DimensionMonotonicity.ycond_glAct_le
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T22:27:33.291354+00:00
-- url     : https://prove2.me/theorems/f529183d-05b9-4f80-86ce-9911fcd3c900
-- title:
--   Dimension Monotonicity: ycond gl Act le
-- statement:
--   The Dimension Monotonicity construction uses the ycond gl Act le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MahlerMeasure/MahlerMeasureProofs/WeightSpaceDimensionMonotone.lean#L1592-L1598
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MahlerMeasure/MahlerMeasureProofs/WeightSpaceDimensionMonotone.lean#L1592-L1598

import Definitions.Def_Formalism_MahlerMeasure_StatementTM
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_FreezeY
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_FreezeBij
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_FreezeInto
import Mathlib
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_WeightSpaceDimensionMonotone
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.GM Formalism.GM.DimensionMonotonicity
open MvPolynomial Finset Formalism.GM.M
variable {p : ℕ} [Fact p.Prime] {N r : ℕ}

theorem Formalism.GM.DimensionMonotonicity.ycond_glAct_le [NeZero r] (LL : Letters N) {J j0 : ℕ} (hJ : J ≤ j0) (M : WithTop ℤ) (c d : Fin r)
    {F : MvPolynomial (Fin N × Fin r) ℚ_[p]} (hF : F ∈ YCond p LL J M) :
    glAct p LL j0 c d F ∈ YCond p LL J M := by sorry
