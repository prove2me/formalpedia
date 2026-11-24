-- Prove2me | Theorems.Thm_Formalism_GM_DimensionMonotonicity_vec_eta
-- name    : Formalism.GM.DimensionMonotonicity.vec_eta
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T22:36:53.260479+00:00
-- url     : https://prove2.me/theorems/a6865b86-6bd4-406e-a91d-411259ce394a
-- title:
--   Dimension Monotonicity: vec eta
-- statement:
--   The Dimension Monotonicity construction uses the vec eta property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MahlerMeasure/MahlerMeasureProofs/WeightSpaceDimensionMonotone.lean#L1988-L1990
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MahlerMeasure/MahlerMeasureProofs/WeightSpaceDimensionMonotone.lean#L1988-L1990

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

theorem Formalism.GM.DimensionMonotonicity.vec_eta (LL : Letters N) (T : TieData) (hadm : T.Admissible LL) (i : Fin T.t) (h : T.pos i + 1 < N) :
    LL.vec ⟨T.pos i + 1, h⟩ = false := by sorry
