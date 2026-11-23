-- Prove2me | Theorems.Thm_Formalism_DivisionValues_ValuationRepresentative_absNorm_map_ringEquiv
-- name    : Formalism.DivisionValues.ValuationRepresentative.absNorm_map_ringEquiv
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T06:57:17.906146+00:00
-- url     : https://prove2.me/theorems/7615bffc-9c32-4cc0-9706-c15300c4b5a2
-- title:
--   Valuation Representative: abs Norm map ring Equiv
-- statement:
--   The Valuation Representative construction uses the abs Norm map ring Equiv property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/QuotientMetricDivisors/HermitianTwistDivisors/ValBasic.lean#L121-L126
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/QuotientMetricDivisors/HermitianTwistDivisors/ValBasic.lean#L121-L126

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

theorem Formalism.DivisionValues.ValuationRepresentative.absNorm_map_ringEquiv {S : Type*} [CommRing S] [IsDedekindDomain S]
    [Module.Free ℤ S] [Module.Finite ℤ S] (g : S ≃+* S) (I : Ideal S) :
    Ideal.absNorm (I.map g) = Ideal.absNorm I := by sorry
