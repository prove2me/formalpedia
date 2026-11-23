-- Prove2me | Theorems.Thm_Formalism_ELL_FormalGroupPointsHom_case_inv
-- name    : Formalism.ELL.FormalGroupPointsHom.case_inv
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T18:09:53.938718+00:00
-- url     : https://prove2.me/theorems/b7241431-53e8-4e0f-9a69-d09b6bd48908
-- title:
--   Formal Group Points Hom: case inv
-- statement:
--   The Formal Group Points Hom construction uses the case inv property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/EllipticTorsion/EllipticTorsionProofs/FormalGroupPointsHomDef.lean#L1083-L1135
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/EllipticTorsion/EllipticTorsionProofs/FormalGroupPointsHomDef.lean#L1083-L1135

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

theorem Formalism.ELL.FormalGroupPointsHom.case_inv (hU : WSubstUnique.{u}) (hS : WChordSubst.{u}) {W : WeierstrassCurve K}
    {w : PowerSeries K} (hW : IntegralModel W) (hw : WFixed W w) (F : FormalGroup K)
    (hFi : IntegralMv F.toPowerSeries)
    (hch : ChordAt W w (MvPowerSeries.X 0) (MvPowerSeries.X 1) F.toPowerSeries) {a : K}
    (ha : ‖a‖ < 1) (hwa : evalPS w a ≠ 0) :
    evalMv2 F.toPowerSeries a
      (-(a / evalPS w a) / W.toAffine.negY (a / evalPS w a) (-1 / evalPS w a)) = 0 := by sorry
