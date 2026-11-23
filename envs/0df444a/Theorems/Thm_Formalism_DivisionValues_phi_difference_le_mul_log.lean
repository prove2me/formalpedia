-- Prove2me | Theorems.Thm_Formalism_DivisionValues_phi_difference_le_mul_log
-- name    : Formalism.DivisionValues.phi_difference_le_mul_log
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T17:23:21.00808+00:00
-- url     : https://prove2.me/theorems/680c5b3a-21b9-464a-89a3-8af0067d5487
-- title:
--   Division Values: phi difference le mul log
-- statement:
--   The Division Values construction uses the phi difference le mul log property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/QuotientMetricDivisors/HermitianTwistDivisors/SecondComplementParameterBounds.lean#L542-L563
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/QuotientMetricDivisors/HermitianTwistDivisors/SecondComplementParameterBounds.lean#L542-L563

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

theorem Formalism.DivisionValues.phi_difference_le_mul_log (y y' : ℝ) (h1 : 1 ≤ y') (h : y' ≤ y) :
    0 ≤ Formalism.LatticeIndexTer.ph y - Formalism.LatticeIndexTer.ph y' ∧ Formalism.LatticeIndexTer.ph y - Formalism.LatticeIndexTer.ph y' ≤ (y - y') * Real.log y := by sorry
