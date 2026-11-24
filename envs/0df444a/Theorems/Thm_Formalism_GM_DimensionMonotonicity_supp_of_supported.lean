-- Prove2me | Theorems.Thm_Formalism_GM_DimensionMonotonicity_supp_of_supported
-- name    : Formalism.GM.DimensionMonotonicity.supp_of_supported
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T22:36:48.300094+00:00
-- url     : https://prove2.me/theorems/14524565-f954-4c52-ab93-aa9fe0090cc5
-- title:
--   Dimension Monotonicity: supp of supported
-- statement:
--   The Dimension Monotonicity construction uses the supp of supported property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MahlerMeasure/MahlerMeasureProofs/WeightSpaceDimensionMonotone.lean#L1239-L1245
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MahlerMeasure/MahlerMeasureProofs/WeightSpaceDimensionMonotone.lean#L1239-L1245

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

theorem Formalism.GM.DimensionMonotonicity.supp_of_supported {K σ : Type} [CommSemiring K] {s : Set σ} {q : MvPolynomial σ K}
    (hq : q ∈ MvPolynomial.supported K s) : ∀ m ∈ q.support, ∀ v, m v ≠ 0 → v ∈ s := by sorry
