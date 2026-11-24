-- Prove2me | Theorems.Thm_Formalism_GM_DimensionMonotonicity_GlW_isWt_pow
-- name    : Formalism.GM.DimensionMonotonicity.GlW.isWt_pow
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T22:27:54.9223+00:00
-- url     : https://prove2.me/theorems/83b96db6-bccd-40ae-87a4-4ce88c73b354
-- title:
--   Gl W: is Wt pow
-- statement:
--   The Gl W construction uses the is Wt pow property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MahlerMeasure/MahlerMeasureProofs/WeightSpaceDimensionMonotone.lean#L451-L464
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MahlerMeasure/MahlerMeasureProofs/WeightSpaceDimensionMonotone.lean#L451-L464

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

theorem Formalism.GM.DimensionMonotonicity.GlW.isWt_pow {ν : Fin r → ℤ} {x : V} (h : G.IsWt ν x) (a b : Fin r) (k : ℕ) :
    G.IsWt (ν + (k : ℤ) • dl a b) ((G.E a b ^ k) x) := by sorry
