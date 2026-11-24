-- Prove2me | Theorems.Thm_Formalism_GM_DimensionMonotonicity_cprod_ne
-- name    : Formalism.GM.DimensionMonotonicity.cprod_ne
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T22:26:34.534031+00:00
-- url     : https://prove2.me/theorems/7d0a0f9b-ce8b-488c-a5cd-6a7eefb05713
-- title:
--   Dimension Monotonicity: cprod ne
-- statement:
--   The Dimension Monotonicity construction uses the cprod ne property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MahlerMeasure/MahlerMeasureProofs/WeightSpaceDimensionMonotone.lean#L2317-L2325
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MahlerMeasure/MahlerMeasureProofs/WeightSpaceDimensionMonotone.lean#L2317-L2325

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

theorem Formalism.GM.DimensionMonotonicity.cprod_ne {K V : Type} [Field K] [CharZero K] (e : ℤ) (cs : List ℤ) (h : ∀ c ∈ cs, c ≠ e) :
    (cs.map (fun c => (((e - c : ℤ)) : K))).prod ≠ 0 := by sorry
