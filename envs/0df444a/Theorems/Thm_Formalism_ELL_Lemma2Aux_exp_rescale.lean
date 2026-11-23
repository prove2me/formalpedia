-- Prove2me | Theorems.Thm_Formalism_ELL_Lemma2Aux_exp_rescale
-- name    : Formalism.ELL.Lemma2Aux.exp_rescale
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T18:18:22.177102+00:00
-- url     : https://prove2.me/theorems/f03a9170-50bd-4fc4-b50a-2117058a0ddc
-- title:
--   Lemma2 Aux: exp rescale
-- statement:
--   The Lemma2 Aux construction uses the exp rescale property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/EllipticTorsion/EllipticTorsionProofs/CoefficientWeightsLemmaTwo.lean#L158-L172
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/EllipticTorsion/EllipticTorsionProofs/CoefficientWeightsLemmaTwo.lean#L158-L172

import Mathlib
import Definitions.Def_Formalism_EllipticTorsion_EllipticTorsionWeights
import Definitions.Def_Formalism_EllipticTorsion_EllipticTorsionProofs_CompExp
import Definitions.Def_Formalism_FormalGroupLog_LogDeterminesLaw
import Definitions.Def_Formalism_EllipticTorsion_EllipticTorsionProofs_CoefficientWeightsLemmaTwo
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open PowerSeries
open Formalism Formalism.ELL Formalism.ELL.Lemma2Aux
variable {K : Type*} [NormedField K] [IsUltrametricDist K]
open Formalism.G

theorem Formalism.ELL.Lemma2Aux.exp_rescale (l E : PowerSeries K) (ζ : K) (hE0 : constantCoeff E = 0) (hl0 : constantCoeff l = 0)
    (hEl : E.subst l = X) (hlE : l.subst E = X) (hlz : (l.subst (ζ • X : PowerSeries K) : PowerSeries K) = ζ • l) :
    (E.subst (ζ • X : PowerSeries K) : PowerSeries K) = ζ • E := by sorry
