-- Prove2me | Theorems.Thm_Formalism_GM_DimensionMonotonicity_glAct_split
-- name    : Formalism.GM.DimensionMonotonicity.glAct_split
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T22:26:33.677028+00:00
-- url     : https://prove2.me/theorems/3031cb6e-07d1-4f48-8721-8598b45cd979
-- title:
--   Dimension Monotonicity: gl Act split
-- statement:
--   The Dimension Monotonicity construction uses the gl Act split property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MahlerMeasure/MahlerMeasureProofs/WeightSpaceDimensionMonotone.lean#L1512-L1524
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MahlerMeasure/MahlerMeasureProofs/WeightSpaceDimensionMonotone.lean#L1512-L1524

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

theorem Formalism.GM.DimensionMonotonicity.glAct_split (LL : Letters N) {J j0 : ℕ} (hJ : J ≤ j0) (c d : Fin r) :
    glAct p LL j0 c d = glAct p LL J c d + midAct p LL J j0 c d := by sorry
