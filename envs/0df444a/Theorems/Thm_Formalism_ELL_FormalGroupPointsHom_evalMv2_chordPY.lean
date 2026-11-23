-- Prove2me | Theorems.Thm_Formalism_ELL_FormalGroupPointsHom_evalMv2_chordPY
-- name    : Formalism.ELL.FormalGroupPointsHom.evalMv2_chordPY
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T18:10:09.535961+00:00
-- url     : https://prove2.me/theorems/18c9f4c8-c57f-4973-8c30-618cbe9c7e6a
-- title:
--   Formal Group Points Hom: eval Mv2 chord PY
-- statement:
--   The Formal Group Points Hom construction uses the eval Mv2 chord PY property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/EllipticTorsion/EllipticTorsionProofs/FormalGroupPointsHomDef.lean#L821-L828
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/EllipticTorsion/EllipticTorsionProofs/FormalGroupPointsHomDef.lean#L821-L828

import Definitions.Def_Formalism_EllipticTorsion_FormalGroupPointsParametrisation
import Definitions.Def_Formalism_EllipticTorsion_EllipticTorsionProofs_ExistsUnitFactor
import Definitions.Def_Formalism_EllipticTorsion_EllipticTorsionProofs_WPoint
import Definitions.Def_Formalism_EllipticTorsion_EllipticTorsionProofs_WSubst
import Definitions.Def_Formalism_EllipticTorsion_EllipticTorsionProofs_WChord
import Definitions.Def_Formalism_EllipticTorsion_EllipticTorsionProofs_NDeriv
import Definitions.Def_Formalism_EllipticTorsion_EllipticTorsionProofs_FormalGroupPointsHomDef
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open PowerSeries
universe u
noncomputable section
open Formalism Formalism.ELL Formalism.ELL.FormalGroupPointsHom
open Formalism.ELL Formalism.G
variable {K : Type u} [NormedField K] [IsUltrametricDist K] [CompleteSpace K]

theorem Formalism.ELL.FormalGroupPointsHom.evalMv2_chordPY {a1 a3 z1 z2 w1 w2 c v : MvPowerSeries (Fin 2) K} (h1 : IntegralMv a1)
    (h2 : IntegralMv a3) (h3 : IntegralMv z1) (h4 : IntegralMv z2) (h5 : IntegralMv w1)
    (h6 : IntegralMv w2) (h7 : IntegralMv c) (h8 : IntegralMv v) {a b : K} (ha : ‖a‖ < 1)
    (hb : ‖b‖ < 1) :
    evalMv2 (chordPY a1 a3 z1 z2 w1 w2 c v) a b = chordPY (evalMv2 a1 a b) (evalMv2 a3 a b)
      (evalMv2 z1 a b) (evalMv2 z2 a b) (evalMv2 w1 a b) (evalMv2 w2 a b) (evalMv2 c a b)
      (evalMv2 v a b) := by sorry
