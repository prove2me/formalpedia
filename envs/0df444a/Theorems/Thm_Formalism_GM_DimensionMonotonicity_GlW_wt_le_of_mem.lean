-- Prove2me | Theorems.Thm_Formalism_GM_DimensionMonotonicity_GlW_wt_le_of_mem
-- name    : Formalism.GM.DimensionMonotonicity.GlW.wt_le_of_mem
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T22:26:25.153082+00:00
-- url     : https://prove2.me/theorems/d34dc4f3-b5d6-4ea7-9741-deefba9ed42c
-- title:
--   Gl W: wt le of mem
-- statement:
--   The Gl W construction uses the wt le of mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MahlerMeasure/MahlerMeasureProofs/WeightSpaceDimensionMonotone.lean#L646-L656
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MahlerMeasure/MahlerMeasureProofs/WeightSpaceDimensionMonotone.lean#L646-L656

import Definitions.Def_Formalism_MahlerMeasure_StatementTM
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_FreezeY
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_FreezeBij
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_FreezeInto
import Mathlib
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_WeightSpaceDimensionMonotone
import Theorems.Thm_Formalism_GM_FrozenVariableComponents_wt_le_of_mem

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

theorem Formalism.GM.DimensionMonotonicity.GlW.wt_le_of_mem {la : Fin r → ℤ} {v : V} (hv : G.IsHW la v) {x : V} (hx : x ∈ G.gS {v})
    {ν : Fin r → ℤ} (h : G.comp ν x ≠ 0) : Dle ν la := by sorry
