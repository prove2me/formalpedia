-- Prove2me | Theorems.Thm_Formalism_DivisionValues_phi_sum_difference_cluster
-- name    : Formalism.DivisionValues.phi_sum_difference_cluster
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T17:23:26.029798+00:00
-- url     : https://prove2.me/theorems/61186e18-f39c-4d20-8472-196c9ab6b2f7
-- title:
--   Division Values: phi sum difference cluster
-- statement:
--   The Division Values construction uses the phi sum difference cluster property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/QuotientMetricDivisors/HermitianTwistDivisors/SecondComplementParameterBounds.lean#L595-L616
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/QuotientMetricDivisors/HermitianTwistDivisors/SecondComplementParameterBounds.lean#L595-L616

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

theorem Formalism.DivisionValues.phi_sum_difference_cluster (n : ℕ) (w Sc A La lo : ℝ) (c c' : Fin n → ℝ) (hw : 1 ≤ w) (hA : w + Sc ≤ A)
    (hc : ∀ i, 0 ≤ c i ∧ c i ≤ Sc) (hc' : ∀ i, 0 ≤ c' i ∧ c' i ≤ Sc) (hLa : La = Real.log A)
    (hLa0 : 0 ≤ La) (hlo : |lo| ≤ La) :
    |(∑ i, Formalism.LatticeIndexTer.ph (w + c i) - (∑ i, (w + c i)) * lo) -
      (∑ i, Formalism.LatticeIndexTer.ph (w + c' i) - (∑ i, (w + c' i)) * lo)| ≤ 2 * ((n : ℝ) * Sc * La) := by sorry
