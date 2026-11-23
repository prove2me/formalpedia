-- Prove2me | Theorems.Thm_Formalism_ELL_Lemma2Aux_add_identity
-- name    : Formalism.ELL.Lemma2Aux.add_identity
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T18:18:11.326306+00:00
-- url     : https://prove2.me/theorems/c38ea6cb-e766-459a-b604-9a62931bffd4
-- title:
--   Lemma2 Aux: add identity
-- statement:
--   The Lemma2 Aux construction uses the add identity property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/EllipticTorsion/EllipticTorsionProofs/CoefficientWeightsLemmaTwo.lean#L91-L130
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/EllipticTorsion/EllipticTorsionProofs/CoefficientWeightsLemmaTwo.lean#L91-L130

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

theorem Formalism.ELL.Lemma2Aux.add_identity (Fs : MvPowerSeries (Fin 2) K) (hFc : MvPowerSeries.constantCoeff Fs = 0)
    (l E g : PowerSeries K) (hl0 : constantCoeff l = 0) (hlF : l.subst Fs = atX l + atY l)
    (hE0 : constantCoeff E = 0) (hEl : E.subst l = X) (hlE : l.subst E = X) :
    MvPowerSeries.subst (fun i : Fin 2 => E.subst (MvPowerSeries.X i : MvPowerSeries (Fin 2) K))
        (g.subst Fs - atX g - atY g) =
      PowerSeries.subst (MvPowerSeries.X 0 + MvPowerSeries.X 1 : MvPowerSeries (Fin 2) K) (PowerSeries.subst E g)
        - PowerSeries.subst (MvPowerSeries.X 0 : MvPowerSeries (Fin 2) K) (PowerSeries.subst E g)
        - PowerSeries.subst (MvPowerSeries.X 1 : MvPowerSeries (Fin 2) K) (PowerSeries.subst E g) := by sorry
