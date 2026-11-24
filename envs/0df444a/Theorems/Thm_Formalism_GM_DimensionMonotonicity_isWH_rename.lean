-- Prove2me | Theorems.Thm_Formalism_GM_DimensionMonotonicity_isWH_rename
-- name    : Formalism.GM.DimensionMonotonicity.isWH_rename
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T22:36:40.750919+00:00
-- url     : https://prove2.me/theorems/88775dc5-6343-467e-b029-59e6eb00d2fc
-- title:
--   Dimension Monotonicity: is WH rename
-- statement:
--   The Dimension Monotonicity construction uses the is WH rename property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MahlerMeasure/MahlerMeasureProofs/WeightSpaceDimensionMonotone.lean#L1226-L1237
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MahlerMeasure/MahlerMeasureProofs/WeightSpaceDimensionMonotone.lean#L1226-L1237

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

theorem Formalism.GM.DimensionMonotonicity.isWH_rename {σ τ M : Type} [AddCommMonoid M] {K : Type} [CommSemiring K] (w : τ → M) (f : σ → τ)
    (hf : Function.Injective f) {F : MvPolynomial σ K} {ν : M} (hF : IsWeightedHomogeneous (w ∘ f) F ν) :
    IsWeightedHomogeneous w (rename f F) ν := by sorry
