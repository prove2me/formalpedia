-- Prove2me | Theorems.Thm_Formalism_GM_DimensionMonotonicity_GlW_ht_add_dl
-- name    : Formalism.GM.DimensionMonotonicity.GlW.ht_add_dl
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T22:46:23.244379+00:00
-- url     : https://prove2.me/theorems/498c84d0-1335-4c4e-a579-e8f894150b46
-- title:
--   Gl W: ht add dl
-- statement:
--   The Gl W construction uses the ht add dl property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MahlerMeasure/MahlerMeasureProofs/WeightSpaceDimensionMonotone.lean#L739-L743
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MahlerMeasure/MahlerMeasureProofs/WeightSpaceDimensionMonotone.lean#L739-L743

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

theorem Formalism.GM.DimensionMonotonicity.GlW.ht_add_dl (μ : Fin r → ℤ) (a b : Fin r) : ht (μ + dl a b) = ht μ + ((b : ℤ) - a) := by sorry
