-- Prove2me | Theorems.Thm_Formalism_DivisionValues_PlaceSumConjugation_finsum_over
-- name    : Formalism.DivisionValues.PlaceSumConjugation.finsum_over
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-22T23:59:36.200713+00:00
-- url     : https://prove2.me/theorems/911d0bbd-5793-4103-b8f8-873e440064e1
-- title:
--   Place Sum Conjugation: finsum over
-- statement:
--   The Place Sum Conjugation construction uses the finsum over property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/QuotientMetricDivisors/HermitianTwistDivisors/SecondComplementParameterBounds.lean#L57-L60
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/QuotientMetricDivisors/HermitianTwistDivisors/SecondComplementParameterBounds.lean#L57-L60

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
variable {K : Type} [Field K] [NumberField K]

theorem Formalism.DivisionValues.PlaceSumConjugation.finsum_over {g : ℕ} (hS : {w : HeightOneSpectrum (𝓞 K) | PlOver g w}.Finite)
    (f : HeightOneSpectrum (𝓞 K) → ℝ) :
    ∑ᶠ (w : HeightOneSpectrum (𝓞 K)) (_ : PlOver g w), f w = ∑ w ∈ hS.toFinset, f w := by sorry
