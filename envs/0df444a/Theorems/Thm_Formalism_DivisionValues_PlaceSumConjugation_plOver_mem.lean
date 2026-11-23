-- Prove2me | Theorems.Thm_Formalism_DivisionValues_PlaceSumConjugation_plOver_mem
-- name    : Formalism.DivisionValues.PlaceSumConjugation.plOver_mem
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T14:16:45.822507+00:00
-- url     : https://prove2.me/theorems/eeaffab4-a74b-4a83-8c38-24bdaa838288
-- title:
--   Place Sum Conjugation: pl Over mem
-- statement:
--   The Place Sum Conjugation construction uses the pl Over mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/QuotientMetricDivisors/HermitianTwistDivisors/SecondComplementParameterBounds.lean#L62-L76
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/QuotientMetricDivisors/HermitianTwistDivisors/SecondComplementParameterBounds.lean#L62-L76

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

theorem Formalism.DivisionValues.PlaceSumConjugation.plOver_mem {g : ℕ} (hg : 0 < g) (w : HeightOneSpectrum (𝓞 K)) (h : PlOver g w) :
    (g : 𝓞 K) ∈ w.asIdeal := by sorry
