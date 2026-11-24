-- Prove2me | Theorems.Thm_Formalism_GM_DimensionMonotonicity_ycond_of_comm
-- name    : Formalism.GM.DimensionMonotonicity.ycond_of_comm
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T22:26:26.276569+00:00
-- url     : https://prove2.me/theorems/52ec0e10-966e-4055-b575-1e8721f3c122
-- title:
--   Dimension Monotonicity: ycond of comm
-- statement:
--   The Dimension Monotonicity construction uses the ycond of comm property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MahlerMeasure/MahlerMeasureProofs/WeightSpaceDimensionMonotone.lean#L1444-L1484
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MahlerMeasure/MahlerMeasureProofs/WeightSpaceDimensionMonotone.lean#L1444-L1484

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

theorem Formalism.GM.DimensionMonotonicity.ycond_of_comm [NeZero r] (LL : Letters N) (J : ℕ) (M : WithTop ℤ)
    (A : MvPolynomial (Fin N × Fin r) ℚ_[p] →ₗ[ℚ_[p]] MvPolynomial (Fin N × Fin r) ℚ_[p])
    (hc : ∀ c d F, A (glAct p LL J c d F) = glAct p LL J c d (A F))
    (hw : ∀ ν F, F ∈ weightedHomogeneousSubmodule ℚ_[p] (wv LL J) ν →
      A F ∈ weightedHomogeneousSubmodule ℚ_[p] (wv LL J) ν) :
    ∀ F ∈ YCond p LL J M, A F ∈ YCond p LL J M := by sorry
