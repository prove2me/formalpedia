-- Prove2me | Theorems.Thm_Formalism_GM_DimensionMonotonicity_wv_snoc_castSucc
-- name    : Formalism.GM.DimensionMonotonicity.wv_snoc_castSucc
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T22:48:48.122835+00:00
-- url     : https://prove2.me/theorems/f321e387-96a5-451e-95e2-7b5d520246ad
-- title:
--   Dimension Monotonicity: wv snoc cast Succ
-- statement:
--   The Dimension Monotonicity construction uses the wv snoc cast Succ property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MahlerMeasure/MahlerMeasureProofs/WeightSpaceDimensionMonotone.lean#L1869-L1871
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MahlerMeasure/MahlerMeasureProofs/WeightSpaceDimensionMonotone.lean#L1869-L1871

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
variable {p : ℕ} [Fact p.Prime] {K r : ℕ}

theorem Formalism.GM.DimensionMonotonicity.wv_snoc_castSucc (LL : Letters K) (n : ℕ) (i : Fin K) (c : Fin r) :
    wv (LL.snoc n) (K + 1) (Fin.castSucc i, c) = wv LL K (i, c) := by sorry
