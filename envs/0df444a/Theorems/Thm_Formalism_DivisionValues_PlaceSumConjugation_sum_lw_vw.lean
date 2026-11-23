-- Prove2me | Theorems.Thm_Formalism_DivisionValues_PlaceSumConjugation_sum_lw_vw
-- name    : Formalism.DivisionValues.PlaceSumConjugation.sum_lw_vw
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-22T23:59:48.253945+00:00
-- url     : https://prove2.me/theorems/ac8fb124-40a3-485b-8f3c-031c3a9e4a36
-- title:
--   Place Sum Conjugation: sum lw vw
-- statement:
--   The Place Sum Conjugation construction uses the sum lw vw property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/QuotientMetricDivisors/HermitianTwistDivisors/SecondComplementParameterBounds.lean#L132-L168
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/QuotientMetricDivisors/HermitianTwistDivisors/SecondComplementParameterBounds.lean#L132-L168

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

theorem Formalism.DivisionValues.PlaceSumConjugation.sum_lw_vw (K : Type) [Field K] [NumberField K] [StarRing K] [IsTotallyComplex K] {g : ℕ}
    (hg : 0 < g) (hS : {w : HeightOneSpectrum (𝓞 K) | PlOver g w}.Finite) :
    ∑ w ∈ hS.toFinset, lw w * (vw w (g : K) : ℝ) = Real.log g := by sorry
