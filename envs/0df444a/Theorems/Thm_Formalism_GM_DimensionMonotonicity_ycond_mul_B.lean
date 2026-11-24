-- Prove2me | Theorems.Thm_Formalism_GM_DimensionMonotonicity_ycond_mul_B
-- name    : Formalism.GM.DimensionMonotonicity.ycond_mul_B
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T22:28:11.629809+00:00
-- url     : https://prove2.me/theorems/21a3e43a-2da2-441c-83ad-e7ae2904d5a9
-- title:
--   Dimension Monotonicity: ycond mul B
-- statement:
--   The Dimension Monotonicity construction uses the ycond mul B property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MahlerMeasure/MahlerMeasureProofs/WeightSpaceDimensionMonotone.lean#L1486-L1506
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MahlerMeasure/MahlerMeasureProofs/WeightSpaceDimensionMonotone.lean#L1486-L1506

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

theorem Formalism.GM.DimensionMonotonicity.ycond_mul_B [NeZero r] (LL : Letters N) {J j0 : ℕ} (hJ : J ≤ j0) (M : WithTop ℤ)
    {q : MvPolynomial (Fin N × Fin r) ℚ_[p]}
    (hq : ∀ m ∈ q.support, ∀ v : Fin N × Fin r, (v.1 : ℕ) < j0 → m v = 0) :
    ∀ F ∈ YCond p LL J M, q * F ∈ YCond p LL J M := by sorry
