-- Prove2me | Theorems.Thm_Formalism_ELL_FormalGroupPointsHom_case_chord
-- name    : Formalism.ELL.FormalGroupPointsHom.case_chord
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T18:10:17.711432+00:00
-- url     : https://prove2.me/theorems/df41913d-f406-4093-97c2-e479f264b6eb
-- title:
--   Formal Group Points Hom: case chord
-- statement:
--   The Formal Group Points Hom construction uses the case chord property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/EllipticTorsion/EllipticTorsionProofs/FormalGroupPointsHomDef.lean#L909-L984
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/EllipticTorsion/EllipticTorsionProofs/FormalGroupPointsHomDef.lean#L909-L984

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

theorem Formalism.ELL.FormalGroupPointsHom.case_chord (hU : WSubstUnique.{u}) {W : WeierstrassCurve K} {w : PowerSeries K}
    (hW : IntegralModel W) (hw : WFixed W w) (F : FormalGroup K) (hFi : IntegralMv F.toPowerSeries)
    (hch : ChordAt W w (MvPowerSeries.X 0) (MvPowerSeries.X 1) F.toPowerSeries) {a b : K}
    (ha : ‖a‖ < 1) (hb : ‖b‖ < 1) (hwa : evalPS w a ≠ 0) (hwb : evalPS w b ≠ 0)
    (hN : a * evalPS w b - b * evalPS w a ≠ 0) :
    -(W.toAffine.addX (a / evalPS w a) (b / evalPS w b)
        ((-1 / evalPS w a - -1 / evalPS w b) / (a / evalPS w a - b / evalPS w b))) /
      W.toAffine.addY (a / evalPS w a) (b / evalPS w b) (-1 / evalPS w a)
        ((-1 / evalPS w a - -1 / evalPS w b) / (a / evalPS w a - b / evalPS w b)) =
      evalMv2 F.toPowerSeries a b := by sorry
