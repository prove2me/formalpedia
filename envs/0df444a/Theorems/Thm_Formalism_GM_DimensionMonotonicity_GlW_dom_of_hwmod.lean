-- Prove2me | Theorems.Thm_Formalism_GM_DimensionMonotonicity_GlW_dom_of_hwmod
-- name    : Formalism.GM.DimensionMonotonicity.GlW.dom_of_hwmod
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T22:26:03.109527+00:00
-- url     : https://prove2.me/theorems/c27e868a-2ea4-4ba9-8ec6-755bef83ce60
-- title:
--   Gl W: dom of hwmod
-- statement:
--   The Gl W construction uses the dom of hwmod property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MahlerMeasure/MahlerMeasureProofs/WeightSpaceDimensionMonotone.lean#L513-L556
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MahlerMeasure/MahlerMeasureProofs/WeightSpaceDimensionMonotone.lean#L513-L556

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

theorem Formalism.GM.DimensionMonotonicity.GlW.dom_of_hwmod {U W : Submodule K V} (hU : G.Stable U) (hW : G.Stable W) (hWf : G.FinW W)
    {μ : Fin r → ℤ} {v : V} (hvW : v ∈ W) (hvU : v ∉ U) (hv : G.IsWt μ v)
    (hr : ∀ a b, a < b → G.E a b v ∈ U) : DomW μ := by sorry
