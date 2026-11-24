-- Prove2me | Theorems.Thm_Formalism_GM_DimensionMonotonicity_choose_tie
-- name    : Formalism.GM.DimensionMonotonicity.choose_tie
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T22:46:39.996522+00:00
-- url     : https://prove2.me/theorems/ee705680-c4e5-400e-9e6d-4f9d606ff3e9
-- title:
--   Dimension Monotonicity: choose tie
-- statement:
--   The Dimension Monotonicity construction uses the choose tie property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MahlerMeasure/MahlerMeasureProofs/WeightSpaceDimensionMonotone.lean#L1992-L1995
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MahlerMeasure/MahlerMeasureProofs/WeightSpaceDimensionMonotone.lean#L1992-L1995

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

theorem Formalism.GM.DimensionMonotonicity.choose_tie (LL : Letters N) (T : TieData) (hadm : T.Admissible LL) (i : Fin T.t)
    (h : ∃ j, T.pos j + 1 = T.pos i + 1) : Classical.choose h = i := by sorry
