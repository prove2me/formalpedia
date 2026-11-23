-- Prove2me | Theorems.Thm_Formalism_DivisionValues_sum_top
-- name    : Formalism.DivisionValues.sum_top
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T00:43:36.534045+00:00
-- url     : https://prove2.me/theorems/2217f9bf-6d95-49dc-82f8-1a8ebf9a880c
-- title:
--   Division Values: sum top
-- statement:
--   The Division Values construction uses the sum top property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/QuotientMetricDivisors/HermitianTwistDivisors/SecondComplementParameterBounds.lean#L285-L291
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/QuotientMetricDivisors/HermitianTwistDivisors/SecondComplementParameterBounds.lean#L285-L291

import Mathlib
import Definitions.Def_Formalism_QuotientMetricDivisors_Complement2Normaliser
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_ValBasic
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_ProdFormula
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_SecondComplementParameterBounds
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module NumberField IsDedekindDomain Finset
noncomputable section
open Formalism Formalism.DivisionValues
open PlaceSumConjugation

theorem Formalism.DivisionValues.sum_top {Pl : Type} [Fintype Pl] (TT : Finset Pl) [DecidablePred (· ∈ TT)] (f : Pl → ℝ) :
    ∑ t ∈ TT, f t = ∑ ρ, if ρ ∈ TT then f ρ else 0 := by sorry
