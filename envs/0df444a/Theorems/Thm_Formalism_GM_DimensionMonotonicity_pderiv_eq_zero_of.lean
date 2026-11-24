-- Prove2me | Theorems.Thm_Formalism_GM_DimensionMonotonicity_pderiv_eq_zero_of
-- name    : Formalism.GM.DimensionMonotonicity.pderiv_eq_zero_of
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T22:27:44.812138+00:00
-- url     : https://prove2.me/theorems/a067889a-3757-4731-b971-46253c047d44
-- title:
--   Dimension Monotonicity: pderiv eq zero of
-- statement:
--   The Dimension Monotonicity construction uses the pderiv eq zero of property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MahlerMeasure/MahlerMeasureProofs/WeightSpaceDimensionMonotone.lean#L1247-L1252
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MahlerMeasure/MahlerMeasureProofs/WeightSpaceDimensionMonotone.lean#L1247-L1252

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

theorem Formalism.GM.DimensionMonotonicity.pderiv_eq_zero_of {K σ : Type} [CommRing K] {q : MvPolynomial σ K} {v : σ}
    (h : ∀ m ∈ q.support, m v = 0) : pderiv v q = 0 := by sorry
