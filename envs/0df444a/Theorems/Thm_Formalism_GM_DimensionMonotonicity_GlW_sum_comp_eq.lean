-- Prove2me | Theorems.Thm_Formalism_GM_DimensionMonotonicity_GlW_sum_comp_eq
-- name    : Formalism.GM.DimensionMonotonicity.GlW.sum_comp_eq
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T22:46:23.599335+00:00
-- url     : https://prove2.me/theorems/531559d2-722e-4a59-a7b5-6f7c13d79f01
-- title:
--   Gl W: sum comp eq
-- statement:
--   The Gl W construction uses the sum comp eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MahlerMeasure/MahlerMeasureProofs/WeightSpaceDimensionMonotone.lean#L75-L76
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MahlerMeasure/MahlerMeasureProofs/WeightSpaceDimensionMonotone.lean#L75-L76

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

theorem Formalism.GM.DimensionMonotonicity.GlW.sum_comp_eq (x : V) {S : Finset (Fin r → ℤ)} (h : ∀ μ ∉ S, G.comp μ x = 0) :
    x = ∑ μ ∈ S, G.comp μ x := by sorry
