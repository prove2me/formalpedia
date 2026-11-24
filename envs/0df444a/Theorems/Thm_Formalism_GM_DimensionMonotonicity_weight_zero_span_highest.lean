-- Prove2me | Theorems.Thm_Formalism_GM_DimensionMonotonicity_weight_zero_span_highest
-- name    : Formalism.GM.DimensionMonotonicity.weight_zero_span_highest
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T22:48:25.199479+00:00
-- url     : https://prove2.me/theorems/8006efa7-10ec-4d57-b5b5-99f761dda7e1
-- title:
--   Dimension Monotonicity: weight zero span highest
-- statement:
--   The Dimension Monotonicity construction uses the weight zero span highest property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MahlerMeasure/MahlerMeasureProofs/WeightSpaceDimensionMonotone.lean#L2422-L2535
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MahlerMeasure/MahlerMeasureProofs/WeightSpaceDimensionMonotone.lean#L2422-L2535

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

theorem Formalism.GM.DimensionMonotonicity.weight_zero_span_highest [NeZero r] (LL : Letters N) (j0 : ℕ) (iK : Fin N) (hiK : (iK : ℕ) < j0)
    (hvK : LL.vec iK = false) (ρ : Fin r) (hρ : (ρ : ℕ) = r - 1) (la : Fin r → ℤ)
    (F : MvPolynomial (Fin N × Fin r) ℚ_[p]) (hF : (GA p LL j0).IsHW la F) (u : ℕ) :
    ∀ x ∈ Submodule.span ℚ_[p] {x | ∃ g ∈ (GA p LL j0).gS {F},
        ∃ s ∈ weightedHomogeneousSubmodule ℚ_[p] (wOut N r iK) 0 ⊓
          weightedHomogeneousSubmodule ℚ_[p] (wL N r) (Pi.single iK (u : ℤ)), x = g * s},
      (∀ μ, ¬ Dle μ (la - (u : ℤ) • Pi.single ρ 1) → (GA p LL j0).comp μ x = 0) ∧
      (GA p LL j0).comp (la - (u : ℤ) • Pi.single ρ 1) x ∈ Submodule.span ℚ_[p] {X (iK, ρ) ^ u * F} := by sorry
