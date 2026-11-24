-- Prove2me | Theorems.Thm_Formalism_GM_DimensionMonotonicity_GlW_Lw_le_low
-- name    : Formalism.GM.DimensionMonotonicity.GlW.Lw_le_low
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T22:27:58.058736+00:00
-- url     : https://prove2.me/theorems/c3aab0f2-6a2e-4b8c-a000-105b5ced66d5
-- title:
--   Gl W: Lw le low
-- statement:
--   The Gl W construction uses the Lw le low property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MahlerMeasure/MahlerMeasureProofs/WeightSpaceDimensionMonotone.lean#L616-L644
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MahlerMeasure/MahlerMeasureProofs/WeightSpaceDimensionMonotone.lean#L616-L644

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

theorem Formalism.GM.DimensionMonotonicity.GlW.Lw_le_low {la : Fin r → ℤ} {v : V} (hv : G.IsWt la v) :
    G.Lw v ≤ Submodule.span K {v} ⊔ G.Low la := by sorry
