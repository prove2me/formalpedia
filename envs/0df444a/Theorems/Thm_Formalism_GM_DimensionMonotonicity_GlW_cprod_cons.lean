-- Prove2me | Theorems.Thm_Formalism_GM_DimensionMonotonicity_GlW_cprod_cons
-- name    : Formalism.GM.DimensionMonotonicity.GlW.cprod_cons
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T22:26:13.853902+00:00
-- url     : https://prove2.me/theorems/41d679a1-82d3-44b5-894c-a2e45309abd0
-- title:
--   Gl W: cprod cons
-- statement:
--   The Gl W construction uses the cprod cons property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MahlerMeasure/MahlerMeasureProofs/WeightSpaceDimensionMonotone.lean#L784-L788
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MahlerMeasure/MahlerMeasureProofs/WeightSpaceDimensionMonotone.lean#L784-L788

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

theorem Formalism.GM.DimensionMonotonicity.GlW.cprod_cons (c : ℤ) (cs : List ℤ) (x : V) :
    G.cprod (c :: cs) x = G.Cas (G.cprod cs x) - ((c : ℤ) : K) • G.cprod cs x := by sorry
