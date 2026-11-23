-- Prove2me | Theorems.Thm_Formalism_DivisionValues_ValuationRepresentative_gramR_eq
-- name    : Formalism.DivisionValues.ValuationRepresentative.gramR_eq
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T01:50:58.618793+00:00
-- url     : https://prove2.me/theorems/87443b81-3818-4107-a479-1a555f6b0e01
-- title:
--   Valuation Representative: gram R eq
-- statement:
--   The Valuation Representative construction uses the gram R eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/QuotientMetricDivisors/HermitianTwistDivisors/ValBasic.lean#L132-L142
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/QuotientMetricDivisors/HermitianTwistDivisors/ValBasic.lean#L132-L142

import Mathlib
import Definitions.Def_Formalism_QuotientMetricDivisors_ProdFormula
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_ValBasic
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module NumberField IsDedekindDomain
open scoped Matrix
noncomputable section
open Formalism Formalism.DivisionValues
open Formalism.DivisionValues.ValuationRepresentative
variable {K : Type} [Field K] [NumberField K] [StarRing K]

theorem Formalism.DivisionValues.ValuationRepresentative.gramR_eq {K : Type} [Field K] [StarRing K] {D m : ℕ} (Γ : Matrix (Fin D) (Fin D) K)
    (e : Fin m → Fin D → K) :
    gramR Γ e = ((Matrix.of e).map star * Γ * (Matrix.of e).transpose).det := by sorry
