-- Prove2me | Theorems.Thm_Formalism_DivisionValues_phi_difference_near_endpoint
-- name    : Formalism.DivisionValues.phi_difference_near_endpoint
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T17:23:14.819223+00:00
-- url     : https://prove2.me/theorems/5347e1de-788f-4f8f-beac-61c01477d723
-- title:
--   Division Values: phi difference near endpoint
-- statement:
--   The Division Values construction uses the phi difference near endpoint property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/QuotientMetricDivisors/HermitianTwistDivisors/SecondComplementParameterBounds.lean#L618-L627
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/QuotientMetricDivisors/HermitianTwistDivisors/SecondComplementParameterBounds.lean#L618-L627

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

theorem Formalism.DivisionValues.phi_difference_near_endpoint (w a Δ A La lo y y' : ℝ) (hw : 1 ≤ w) (ha : 0 ≤ a) (hy : a ≤ y ∧ y ≤ a + Δ)
    (hy' : a ≤ y' ∧ y' ≤ a + Δ) (hA : y + w ≤ A) (hA' : y' + w ≤ A) (hLa : La = Real.log A)
    (hLa0 : 0 ≤ La) (hlo : |lo| ≤ La) :
    |(Formalism.LatticeIndexTer.ph (y + w) - (y + w) * lo) - (Formalism.LatticeIndexTer.ph (y' + w) - (y' + w) * lo)| ≤
      2 * (Δ * La) := by sorry
