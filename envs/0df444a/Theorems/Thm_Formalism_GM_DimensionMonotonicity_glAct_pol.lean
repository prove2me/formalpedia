-- Prove2me | Theorems.Thm_Formalism_GM_DimensionMonotonicity_glAct_pol
-- name    : Formalism.GM.DimensionMonotonicity.glAct_pol
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T22:26:14.518784+00:00
-- url     : https://prove2.me/theorems/a8e048fa-a064-498d-8ea3-ead8b2b9dfd7
-- title:
--   Dimension Monotonicity: gl Act pol
-- statement:
--   The Dimension Monotonicity construction uses the gl Act pol property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MahlerMeasure/MahlerMeasureProofs/WeightSpaceDimensionMonotone.lean#L1364-L1369
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MahlerMeasure/MahlerMeasureProofs/WeightSpaceDimensionMonotone.lean#L1364-L1369

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

theorem Formalism.GM.DimensionMonotonicity.glAct_pol (LL L2 : Letters N) (j : ℕ) (a b : Fin r) {x : MvPolynomial (Fin N × Fin r) ℚ_[p]}
    (hx : x ∈ Pol p r L2) : glAct p LL j a b x ∈ Pol p r L2 := by sorry
