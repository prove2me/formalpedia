-- Prove2me | Theorems.Thm_Formalism_ELL_Lemma2Aux_coeff_X0_add_X1_pow
-- name    : Formalism.ELL.Lemma2Aux.coeff_X0_add_X1_pow
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T18:17:58.173794+00:00
-- url     : https://prove2.me/theorems/740e14f6-7085-4e27-82d2-19b44790d84d
-- title:
--   Lemma2 Aux: coeff X0 add X1 pow
-- statement:
--   The Lemma2 Aux construction uses the coeff X0 add X1 pow property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/EllipticTorsion/EllipticTorsionProofs/CoefficientWeightsLemmaTwo.lean#L52-L87
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/EllipticTorsion/EllipticTorsionProofs/CoefficientWeightsLemmaTwo.lean#L52-L87

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

theorem Formalism.ELL.Lemma2Aux.coeff_X0_add_X1_pow {R : Type*} [CommRing R] (d i j : ℕ) :
    MvPowerSeries.coeff (Finsupp.single (0 : Fin 2) i + Finsupp.single 1 j)
      ((MvPowerSeries.X 0 + MvPowerSeries.X 1 : MvPowerSeries (Fin 2) R) ^ d) =
      if i + j = d then (d.choose i : R) else 0 := by sorry
