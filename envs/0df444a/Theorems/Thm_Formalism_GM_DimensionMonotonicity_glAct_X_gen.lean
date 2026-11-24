-- Prove2me | Theorems.Thm_Formalism_GM_DimensionMonotonicity_glAct_X_gen
-- name    : Formalism.GM.DimensionMonotonicity.glAct_X_gen
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T22:26:48.329355+00:00
-- url     : https://prove2.me/theorems/9ed33acd-18b0-4844-9bf5-22ae76bc39e5
-- title:
--   Dimension Monotonicity: gl Act X gen
-- statement:
--   The Dimension Monotonicity construction uses the gl Act X gen property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MahlerMeasure/MahlerMeasureProofs/WeightSpaceDimensionMonotone.lean#L1196-L1204
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MahlerMeasure/MahlerMeasureProofs/WeightSpaceDimensionMonotone.lean#L1196-L1204

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
open MvPolynomial Finset Formalism.GM.M
variable {p : ℕ} [Fact p.Prime] {N r : ℕ}

theorem Formalism.GM.DimensionMonotonicity.glAct_X_gen (LL : Letters N) (j : ℕ) (c d : Fin r) (i : Fin N) (a : Fin r) :
    glAct p LL j c d (X (i, a)) = if (i : ℕ) < j then
      (if LL.vec i then (if a = d then X (i, c) else 0) else (if a = c then -X (i, d) else 0)) else 0 := by sorry
