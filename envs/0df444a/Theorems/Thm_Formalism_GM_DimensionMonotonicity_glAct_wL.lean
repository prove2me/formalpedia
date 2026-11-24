-- Prove2me | Theorems.Thm_Formalism_GM_DimensionMonotonicity_glAct_wL
-- name    : Formalism.GM.DimensionMonotonicity.glAct_wL
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T22:27:20.338711+00:00
-- url     : https://prove2.me/theorems/43dde3da-eeb6-4d70-a062-37cce350deb1
-- title:
--   Dimension Monotonicity: gl Act w L
-- statement:
--   The Dimension Monotonicity construction uses the gl Act w L property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MahlerMeasure/MahlerMeasureProofs/WeightSpaceDimensionMonotone.lean#L1338-L1362
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MahlerMeasure/MahlerMeasureProofs/WeightSpaceDimensionMonotone.lean#L1338-L1362

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

theorem Formalism.GM.DimensionMonotonicity.glAct_wL (LL : Letters N) (j : ℕ) (a b : Fin r) {D : Fin N → ℤ} {x : MvPolynomial (Fin N × Fin r) ℚ_[p]}
    (hx : x ∈ weightedHomogeneousSubmodule ℚ_[p] (wL N r) D) :
    glAct p LL j a b x ∈ weightedHomogeneousSubmodule ℚ_[p] (wL N r) D := by sorry
