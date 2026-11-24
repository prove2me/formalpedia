-- Prove2me | Theorems.Thm_Formalism_GM_DimensionMonotonicity_GlW_pow_mem
-- name    : Formalism.GM.DimensionMonotonicity.GlW.pow_mem
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T22:26:20.553966+00:00
-- url     : https://prove2.me/theorems/d9d5a4f1-02fb-4966-98bf-1054b84be281
-- title:
--   Gl W: pow mem
-- statement:
--   The Gl W construction uses the pow mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MahlerMeasure/MahlerMeasureProofs/WeightSpaceDimensionMonotone.lean#L466-L472
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MahlerMeasure/MahlerMeasureProofs/WeightSpaceDimensionMonotone.lean#L466-L472

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
open Finset
open Formalism.GM.DimensionMonotonicity.GlW
variable {K V : Type} [Field K] [CharZero K] [AddCommGroup V] [Module K V] {r : ℕ} (G : GlW K V r)

theorem Formalism.GM.DimensionMonotonicity.GlW.pow_mem {U : Submodule K V} (hU : G.Stable U) (a b : Fin r) (k : ℕ) {x : V} (hx : x ∈ U) :
    (G.E a b ^ k) x ∈ U := by sorry
