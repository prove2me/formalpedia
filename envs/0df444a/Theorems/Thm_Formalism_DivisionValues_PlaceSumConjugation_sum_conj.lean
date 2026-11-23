-- Prove2me | Theorems.Thm_Formalism_DivisionValues_PlaceSumConjugation_sum_conj
-- name    : Formalism.DivisionValues.PlaceSumConjugation.sum_conj
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T14:16:52.585666+00:00
-- url     : https://prove2.me/theorems/d382007c-09d1-40a9-b018-fefec42b0925
-- title:
--   Place Sum Conjugation: sum conj
-- statement:
--   The Place Sum Conjugation construction uses the sum conj property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/QuotientMetricDivisors/HermitianTwistDivisors/SecondComplementParameterBounds.lean#L111-L123
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/QuotientMetricDivisors/HermitianTwistDivisors/SecondComplementParameterBounds.lean#L111-L123

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
open Formalism.DivisionValues.PlaceSumConjugation
variable {K : Type} [Field K] [NumberField K] [StarRing K]

theorem Formalism.DivisionValues.PlaceSumConjugation.sum_conj {g : ℕ} (hS : {w : HeightOneSpectrum (𝓞 K) | PlOver g w}.Finite)
    (f : HeightOneSpectrum (𝓞 K) → ℝ) :
    ∑ w ∈ hS.toFinset, f (conjPl w) = ∑ w ∈ hS.toFinset, f w := by sorry
