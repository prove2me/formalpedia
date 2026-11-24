-- Prove2me | Theorems.Thm_Formalism_GM_DimensionMonotonicity_weight_mapDomain
-- name    : Formalism.GM.DimensionMonotonicity.weight_mapDomain
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T22:26:48.869902+00:00
-- url     : https://prove2.me/theorems/697943c2-d6d9-44f8-a673-1ccc6e7a00d7
-- title:
--   Dimension Monotonicity: weight map Domain
-- statement:
--   The Dimension Monotonicity construction uses the weight map Domain property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MahlerMeasure/MahlerMeasureProofs/WeightSpaceDimensionMonotone.lean#L1216-L1224
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MahlerMeasure/MahlerMeasureProofs/WeightSpaceDimensionMonotone.lean#L1216-L1224

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

theorem Formalism.GM.DimensionMonotonicity.weight_mapDomain {σ τ M : Type} [AddCommMonoid M] (w : τ → M) (f : σ → τ) (m : σ →₀ ℕ) :
    Finsupp.weight w (Finsupp.mapDomain f m) = Finsupp.weight (w ∘ f) m := by sorry
