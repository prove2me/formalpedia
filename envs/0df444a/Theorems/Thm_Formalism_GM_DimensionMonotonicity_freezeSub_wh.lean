-- Prove2me | Theorems.Thm_Formalism_GM_DimensionMonotonicity_freezeSub_wh
-- name    : Formalism.GM.DimensionMonotonicity.freezeSub_wh
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T22:47:41.377105+00:00
-- url     : https://prove2.me/theorems/8cacb323-ee45-47bd-b343-eafe9187005d
-- title:
--   Dimension Monotonicity: freeze Sub wh
-- statement:
--   The Dimension Monotonicity construction uses the freeze Sub wh property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MahlerMeasure/MahlerMeasureProofs/WeightSpaceDimensionMonotone.lean#L1877-L1915
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MahlerMeasure/MahlerMeasureProofs/WeightSpaceDimensionMonotone.lean#L1877-L1915

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

theorem Formalism.GM.DimensionMonotonicity.freezeSub_wh (LL : Letters K) (n : ℕ) (ρ : Fin r) (v : Fin K × Fin r) :
    IsWeightedHomogeneous (wv (LL.snoc n) (K + 1)) (freezeSub p LL ρ v) (wv LL K v - Pi.single ρ 1) := by sorry
