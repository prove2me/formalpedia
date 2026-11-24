-- Prove2me | Theorems.Thm_Formalism_GM_DimensionMonotonicity_Cas_wh
-- name    : Formalism.GM.DimensionMonotonicity.Cas_wh
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T22:45:52.880401+00:00
-- url     : https://prove2.me/theorems/f0c40cdf-77f3-49da-87d1-2e6081284b3d
-- title:
--   Dimension Monotonicity: Cas wh
-- statement:
--   The Dimension Monotonicity construction uses the Cas wh property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MahlerMeasure/MahlerMeasureProofs/WeightSpaceDimensionMonotone.lean#L1621-L1633
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MahlerMeasure/MahlerMeasureProofs/WeightSpaceDimensionMonotone.lean#L1621-L1633

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

theorem Formalism.GM.DimensionMonotonicity.Cas_wh (LL : Letters N) {j0 J : ℕ} (hJ : j0 ≤ J) {ν : Fin r → ℤ} {F : MvPolynomial (Fin N × Fin r) ℚ_[p]}
    (hF : F ∈ weightedHomogeneousSubmodule ℚ_[p] (wv LL J) ν) :
    (GA p LL j0).Cas F ∈ weightedHomogeneousSubmodule ℚ_[p] (wv LL J) ν := by sorry
