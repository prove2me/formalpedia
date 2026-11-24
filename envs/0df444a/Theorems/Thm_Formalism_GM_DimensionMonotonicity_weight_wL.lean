-- Prove2me | Theorems.Thm_Formalism_GM_DimensionMonotonicity_weight_wL
-- name    : Formalism.GM.DimensionMonotonicity.weight_wL
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T22:27:33.427931+00:00
-- url     : https://prove2.me/theorems/17acbc6a-c670-40ad-acc4-ed36031b13f3
-- title:
--   Dimension Monotonicity: weight w L
-- statement:
--   The Dimension Monotonicity construction uses the weight w L property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MahlerMeasure/MahlerMeasureProofs/WeightSpaceDimensionMonotone.lean#L1311-L1318
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MahlerMeasure/MahlerMeasureProofs/WeightSpaceDimensionMonotone.lean#L1311-L1318

import Definitions.Def_Formalism_MahlerMeasure_StatementTM
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_FreezeY
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_FreezeBij
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_FreezeInto
import Mathlib
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_WeightSpaceDimensionMonotone
import Theorems.Thm_Formalism_GM_M_FB_weight_wL

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

theorem Formalism.GM.DimensionMonotonicity.weight_wL (m : Fin N × Fin r →₀ ℕ) (i : Fin N) :
    Finsupp.weight (wL N r) m i = ∑ c, (m (i, c) : ℤ) := by sorry
