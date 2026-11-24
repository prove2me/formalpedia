-- Prove2me | Theorems.Thm_Formalism_GM_DimensionMonotonicity_cprod_mul_B
-- name    : Formalism.GM.DimensionMonotonicity.cprod_mul_B
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T22:47:37.874804+00:00
-- url     : https://prove2.me/theorems/4dfe7115-4572-4cd9-acd2-f1fdf43a5a38
-- title:
--   Dimension Monotonicity: cprod mul B
-- statement:
--   The Dimension Monotonicity construction uses the cprod mul B property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MahlerMeasure/MahlerMeasureProofs/WeightSpaceDimensionMonotone.lean#L2337-L2343
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MahlerMeasure/MahlerMeasureProofs/WeightSpaceDimensionMonotone.lean#L2337-L2343

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

theorem Formalism.GM.DimensionMonotonicity.cprod_mul_B (LL : Letters N) (j0 : ℕ) (cs : List ℤ) (y q : MvPolynomial (Fin N × Fin r) ℚ_[p])
    (hq : ∀ m ∈ q.support, ∀ v : Fin N × Fin r, (v.1 : ℕ) < j0 → m v = 0) :
    (GA p LL j0).cprod cs (y * q) = (GA p LL j0).cprod cs y * q := by sorry
