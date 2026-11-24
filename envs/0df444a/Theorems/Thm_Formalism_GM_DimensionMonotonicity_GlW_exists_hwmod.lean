-- Prove2me | Theorems.Thm_Formalism_GM_DimensionMonotonicity_GlW_exists_hwmod
-- name    : Formalism.GM.DimensionMonotonicity.GlW.exists_hwmod
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T22:25:50.119222+00:00
-- url     : https://prove2.me/theorems/e501c37a-6fcc-4d1d-b5f7-5b33917787e4
-- title:
--   Gl W: exists hwmod
-- statement:
--   The Gl W construction uses the exists hwmod property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MahlerMeasure/MahlerMeasureProofs/WeightSpaceDimensionMonotone.lean#L745-L778
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MahlerMeasure/MahlerMeasureProofs/WeightSpaceDimensionMonotone.lean#L745-L778

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

theorem Formalism.GM.DimensionMonotonicity.GlW.exists_hwmod {W U : Submodule K V} (hWg : G.Graded W) (hWr : G.Raising W) (hWf : G.FinW W)
    (h : ¬ W ≤ U) : ∃ v ∈ W, v ∉ U ∧ ∃ μ, G.IsWt μ v ∧ ∀ a b, a < b → G.E a b v ∈ U := by sorry
