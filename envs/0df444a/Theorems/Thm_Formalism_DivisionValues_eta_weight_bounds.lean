-- Prove2me | Theorems.Thm_Formalism_DivisionValues_eta_weight_bounds
-- name    : Formalism.DivisionValues.eta_weight_bounds
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T14:30:56.496793+00:00
-- url     : https://prove2.me/theorems/1c8b3f61-d8cf-42f7-9ed5-7c079b361e41
-- title:
--   Division Values: eta weight bounds
-- statement:
--   The Division Values construction uses the eta weight bounds property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/QuotientMetricDivisors/HermitianTwistDivisors/SecondComplementParameterBounds.lean#L412-L417
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/QuotientMetricDivisors/HermitianTwistDivisors/SecondComplementParameterBounds.lean#L412-L417

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

theorem Formalism.DivisionValues.eta_weight_bounds (m tt η w'' : ℝ) (hm : 1 ≤ m) (htt : 0 ≤ tt) (hη : 0 ≤ η)
    (h : m * (tt + 1) * η ≤ w'') : m * η ≤ w'' ∧ m * tt * η ≤ w'' := by sorry
