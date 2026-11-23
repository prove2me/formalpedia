-- Prove2me | Theorems.Thm_Formalism_DivisionValues_PlaceSumConjugation_vw_conj_nat
-- name    : Formalism.DivisionValues.PlaceSumConjugation.vw_conj_nat
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-22T21:07:27.428801+00:00
-- url     : https://prove2.me/theorems/cc89db08-25bb-415c-991f-7b6bd7d7dd30
-- title:
--   Place Sum Conjugation: vw conj nat
-- statement:
--   The Place Sum Conjugation construction uses the vw conj nat property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/QuotientMetricDivisors/HermitianTwistDivisors/SecondComplementParameterBounds.lean#L84-L86
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/QuotientMetricDivisors/HermitianTwistDivisors/SecondComplementParameterBounds.lean#L84-L86

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

theorem Formalism.DivisionValues.PlaceSumConjugation.vw_conj_nat (g : ℕ) (w : HeightOneSpectrum (𝓞 K)) :
    vw (conjPl w) (g : K) = vw w (g : K) := by sorry
