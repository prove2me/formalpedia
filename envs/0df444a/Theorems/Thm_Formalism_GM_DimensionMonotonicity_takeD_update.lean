-- Prove2me | Theorems.Thm_Formalism_GM_DimensionMonotonicity_takeD_update
-- name    : Formalism.GM.DimensionMonotonicity.takeD_update
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T22:36:53.705802+00:00
-- url     : https://prove2.me/theorems/09ca39a6-2bf0-4992-842e-24d742c78e9a
-- title:
--   Dimension Monotonicity: take D update
-- statement:
--   The Dimension Monotonicity construction uses the take D update property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MahlerMeasure/MahlerMeasureProofs/WeightSpaceDimensionMonotone.lean#L2003-L2019
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MahlerMeasure/MahlerMeasureProofs/WeightSpaceDimensionMonotone.lean#L2003-L2019

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

theorem Formalism.GM.DimensionMonotonicity.takeD_update (LL : Letters N) (T : TieData) (hadm : T.Admissible LL) (i : Fin T.t) (n : Fin T.t → ℕ) (n' : ℕ) :
    (LL.setTies T (Function.update n i n')).takeD (T.pos i + 1) = (LL.setTies T n).takeD (T.pos i + 1) := by sorry
