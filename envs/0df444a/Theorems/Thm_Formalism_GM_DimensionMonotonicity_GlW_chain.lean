-- Prove2me | Theorems.Thm_Formalism_GM_DimensionMonotonicity_GlW_chain
-- name    : Formalism.GM.DimensionMonotonicity.GlW.chain
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T22:46:28.751842+00:00
-- url     : https://prove2.me/theorems/f9fd438f-1661-400b-82af-5bbf2590ab94
-- title:
--   Gl W: chain
-- statement:
--   The Gl W construction uses the chain property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MahlerMeasure/MahlerMeasureProofs/WeightSpaceDimensionMonotone.lean#L817-L867
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MahlerMeasure/MahlerMeasureProofs/WeightSpaceDimensionMonotone.lean#L817-L867

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

theorem Formalism.GM.DimensionMonotonicity.GlW.chain {W V0 : Submodule K V} [FiniteDimensional K W] (hW : G.Stable W) (hWf : G.FinW W)
    (hV0 : G.Stable V0) (hV0W : V0 ≤ W) (c0 : ℤ)
    (H : ∀ U : Submodule K V, G.Stable U → V0 ≤ U → U ≤ W → ∀ μ v, v ∈ W → v ∉ U → G.IsWt μ v →
      (∀ a b, a < b → G.E a b v ∈ U) → casI μ ≠ c0) :
    ∃ cs : List ℤ, (∀ c ∈ cs, c ≠ c0) ∧ ∀ x ∈ W, G.cprod cs x ∈ V0 := by sorry
