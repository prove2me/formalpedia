-- Prove2me | Theorems.Thm_Formalism_DivisionValues_PlaceSumConjugation_plOver_conj
-- name    : Formalism.DivisionValues.PlaceSumConjugation.plOver_conj
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-22T21:06:58.314395+00:00
-- url     : https://prove2.me/theorems/059b2bc1-aff2-465b-b884-b18709afce86
-- title:
--   Place Sum Conjugation: pl Over conj
-- statement:
--   The Place Sum Conjugation construction uses the pl Over conj property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/QuotientMetricDivisors/HermitianTwistDivisors/SecondComplementParameterBounds.lean#L88-L90
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/QuotientMetricDivisors/HermitianTwistDivisors/SecondComplementParameterBounds.lean#L88-L90

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

theorem Formalism.DivisionValues.PlaceSumConjugation.plOver_conj (g : ℕ) (w : HeightOneSpectrum (𝓞 K)) : PlOver g (conjPl w) ↔ PlOver g w := by sorry
