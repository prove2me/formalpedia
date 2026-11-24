-- Prove2me | Theorems.Thm_Formalism_GM_DimensionMonotonicity_GlW_sl2
-- name    : Formalism.GM.DimensionMonotonicity.GlW.sl2
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T22:46:37.873905+00:00
-- url     : https://prove2.me/theorems/02cb0df0-021d-4979-aaa3-d4bef63beb83
-- title:
--   Gl W: sl2
-- statement:
--   The Gl W construction uses the sl2 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MahlerMeasure/MahlerMeasureProofs/WeightSpaceDimensionMonotone.lean#L474-L511
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MahlerMeasure/MahlerMeasureProofs/WeightSpaceDimensionMonotone.lean#L474-L511

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

theorem Formalism.GM.DimensionMonotonicity.GlW.sl2 {a b : Fin r} (hab : a ≠ b) {ν : Fin r → ℤ} {x : V} (hx : G.IsWt ν x) (k : ℕ) :
    G.E a b ((G.E b a ^ (k + 1)) x) = (G.E b a ^ (k + 1)) (G.E a b x) +
      (((k + 1 : ℕ) : K) * ((ν a - ν b - k : ℤ) : K)) • (G.E b a ^ k) x := by sorry
