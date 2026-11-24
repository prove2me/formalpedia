-- Prove2me | Theorems.Thm_Formalism_GM_DimensionMonotonicity_weight_cov_monomial
-- name    : Formalism.GM.DimensionMonotonicity.weight_cov_monomial
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T22:48:42.01881+00:00
-- url     : https://prove2.me/theorems/9b12b5d6-4f9f-467c-b006-c5a347e38397
-- title:
--   Dimension Monotonicity: weight cov monomial
-- statement:
--   The Dimension Monotonicity construction uses the weight cov monomial property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MahlerMeasure/MahlerMeasureProofs/WeightSpaceDimensionMonotone.lean#L2293-L2304
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MahlerMeasure/MahlerMeasureProofs/WeightSpaceDimensionMonotone.lean#L2293-L2304

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

theorem Formalism.GM.DimensionMonotonicity.weight_cov_monomial (LL : Letters N) (j0 : ℕ) (iK : Fin N) (hiK : (iK : ℕ) < j0) (hv : LL.vec iK = false)
    (m : Fin N × Fin r →₀ ℕ) (hm : ∀ v : Fin N × Fin r, v.1 ≠ iK → m v = 0) :
    Finsupp.weight (wv LL j0) m = fun c => -((m (iK, c) : ℕ) : ℤ) := by sorry
