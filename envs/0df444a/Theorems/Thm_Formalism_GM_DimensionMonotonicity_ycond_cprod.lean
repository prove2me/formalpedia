-- Prove2me | Theorems.Thm_Formalism_GM_DimensionMonotonicity_ycond_cprod
-- name    : Formalism.GM.DimensionMonotonicity.ycond_cprod
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T22:49:00.790094+00:00
-- url     : https://prove2.me/theorems/73d119e1-e62a-40c2-92c4-0ab7ab7caf4c
-- title:
--   Dimension Monotonicity: ycond cprod
-- statement:
--   The Dimension Monotonicity construction uses the ycond cprod property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MahlerMeasure/MahlerMeasureProofs/WeightSpaceDimensionMonotone.lean#L1635-L1649
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MahlerMeasure/MahlerMeasureProofs/WeightSpaceDimensionMonotone.lean#L1635-L1649

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

theorem Formalism.GM.DimensionMonotonicity.ycond_cprod [NeZero r] (LL : Letters N) {j0 J : ℕ} (hJ : j0 ≤ J) (M : WithTop ℤ) (cs : List ℤ)
    {F : MvPolynomial (Fin N × Fin r) ℚ_[p]} (hF : F ∈ YCond p LL J M) :
    (GA p LL j0).cprod cs F ∈ YCond p LL J M := by sorry
