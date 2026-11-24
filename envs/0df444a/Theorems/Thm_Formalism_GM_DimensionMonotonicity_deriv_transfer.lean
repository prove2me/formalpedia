-- Prove2me | Theorems.Thm_Formalism_GM_DimensionMonotonicity_deriv_transfer
-- name    : Formalism.GM.DimensionMonotonicity.deriv_transfer
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T22:27:49.89961+00:00
-- url     : https://prove2.me/theorems/b5ffe93b-6eae-49d4-a775-709d46ddffb9
-- title:
--   Dimension Monotonicity: deriv transfer
-- statement:
--   The Dimension Monotonicity construction uses the deriv transfer property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MahlerMeasure/MahlerMeasureProofs/WeightSpaceDimensionMonotone.lean#L1179-L1192
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MahlerMeasure/MahlerMeasureProofs/WeightSpaceDimensionMonotone.lean#L1179-L1192

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

theorem Formalism.GM.DimensionMonotonicity.deriv_transfer {K σ τ : Type} [CommRing K] (φ : MvPolynomial σ K →ₐ[K] MvPolynomial τ K)
    (D0 : MvPolynomial σ K →ₗ[K] MvPolynomial σ K) (D1 : MvPolynomial τ K →ₗ[K] MvPolynomial τ K)
    (h0 : ∀ x y, D0 (x * y) = x * D0 y + y * D0 x) (h1 : ∀ x y, D1 (x * y) = x * D1 y + y * D1 x)
    (hg : ∀ v, D1 (φ (X v)) = φ (D0 (X v))) (f : MvPolynomial σ K) : D1 (φ f) = φ (D0 f) := by sorry
