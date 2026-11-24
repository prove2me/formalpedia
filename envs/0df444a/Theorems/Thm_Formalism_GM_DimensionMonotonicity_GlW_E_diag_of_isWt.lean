-- Prove2me | Theorems.Thm_Formalism_GM_DimensionMonotonicity_GlW_E_diag_of_isWt
-- name    : Formalism.GM.DimensionMonotonicity.GlW.E_diag_of_isWt
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T22:26:11.413876+00:00
-- url     : https://prove2.me/theorems/1e3982cb-8ca6-4263-9f97-9e3c8e1f89b2
-- title:
--   Gl W: E diag of is Wt
-- statement:
--   The Gl W construction uses the E diag of is Wt property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MahlerMeasure/MahlerMeasureProofs/WeightSpaceDimensionMonotone.lean#L65-L69
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MahlerMeasure/MahlerMeasureProofs/WeightSpaceDimensionMonotone.lean#L65-L69

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

theorem Formalism.GM.DimensionMonotonicity.GlW.E_diag_of_isWt {ν : Fin r → ℤ} {x : V} (h : G.IsWt ν x) (c : Fin r) :
    G.E c c x = ((ν c : ℤ) : K) • x := by sorry
