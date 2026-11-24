-- Prove2me | Theorems.Thm_Formalism_GM_DimensionMonotonicity_GlW_weight_component_mem_submodule
-- name    : Formalism.GM.DimensionMonotonicity.GlW.weight_component_mem_submodule
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T22:46:40.642797+00:00
-- url     : https://prove2.me/theorems/0d9a72f5-da8b-482d-a247-583402d65735
-- title:
--   Gl W: weight component mem submodule
-- statement:
--   The Gl W construction uses the weight component mem submodule property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MahlerMeasure/MahlerMeasureProofs/WeightSpaceDimensionMonotone.lean#L78-L127
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MahlerMeasure/MahlerMeasureProofs/WeightSpaceDimensionMonotone.lean#L78-L127

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
variable {K V : Type} [Field K] [AddCommGroup V] [Module K V] {r : ℕ} (G : GlW K V r)

theorem Formalism.GM.DimensionMonotonicity.GlW.weight_component_mem_submodule [CharZero K] (U : Submodule K V) (hU : ∀ c, ∀ x ∈ U, G.E c c x ∈ U) :
    ∀ (S : Finset (Fin r → ℤ)) (x : V), x ∈ U → (∀ μ ∉ S, G.comp μ x = 0) → ∀ μ, G.comp μ x ∈ U := by sorry
