-- Prove2me | Theorems.Thm_Formalism_GM_DimensionMonotonicity_vec_compat
-- name    : Formalism.GM.DimensionMonotonicity.vec_compat
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T22:26:49.502963+00:00
-- url     : https://prove2.me/theorems/d693701c-8ace-4366-9fc6-dec662d22cb7
-- title:
--   Dimension Monotonicity: vec compat
-- statement:
--   The Dimension Monotonicity construction uses the vec compat property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MahlerMeasure/MahlerMeasureProofs/WeightSpaceDimensionMonotone.lean#L2021-L2036
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MahlerMeasure/MahlerMeasureProofs/WeightSpaceDimensionMonotone.lean#L2021-L2036

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

theorem Formalism.GM.DimensionMonotonicity.vec_compat [NeZero N] (LL : Letters N) (T : TieData) (hadm : T.Admissible LL) (i : Fin T.t)
    (n : Fin T.t → ℕ) (m0 : ℕ) (a : Fin (T.pos i + 1 + 1)) :
    LL.vec (ιF N (T.pos i + 1) a) = (((LL.setTies T n).takeD (T.pos i + 1)).snoc m0).vec a := by sorry
