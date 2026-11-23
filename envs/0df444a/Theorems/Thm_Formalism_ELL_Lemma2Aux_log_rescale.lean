-- Prove2me | Theorems.Thm_Formalism_ELL_Lemma2Aux_log_rescale
-- name    : Formalism.ELL.Lemma2Aux.log_rescale
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T18:18:20.515313+00:00
-- url     : https://prove2.me/theorems/15ed9e58-d19e-461e-9212-799c6f840875
-- title:
--   Lemma2 Aux: log rescale
-- statement:
--   The Lemma2 Aux construction uses the log rescale property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/EllipticTorsion/EllipticTorsionProofs/CoefficientWeightsLemmaTwo.lean#L132-L156
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/EllipticTorsion/EllipticTorsionProofs/CoefficientWeightsLemmaTwo.lean#L132-L156

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

theorem Formalism.ELL.Lemma2Aux.log_rescale [CharZero K] (F : FormalGroup K) (l : PowerSeries K) (ζ : K) (hζ0 : ζ ≠ 0)
    (hl : IsLog F l) (hhom : IsHom F F (ζ • X)) : (l.subst (ζ • X : PowerSeries K) : PowerSeries K) = ζ • l := by sorry
