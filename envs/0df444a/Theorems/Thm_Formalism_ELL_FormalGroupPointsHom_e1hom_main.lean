-- Prove2me | Theorems.Thm_Formalism_ELL_FormalGroupPointsHom_e1hom_main
-- name    : Formalism.ELL.FormalGroupPointsHom.e1hom_main
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T18:11:04.834844+00:00
-- url     : https://prove2.me/theorems/90427832-1dd1-45a7-8542-f38ab3961584
-- title:
--   Formal Group Points Hom: e1hom main
-- statement:
--   The Formal Group Points Hom construction uses the e1hom main property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/EllipticTorsion/EllipticTorsionProofs/FormalGroupPointsHomDef.lean#L1151-L1211
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/EllipticTorsion/EllipticTorsionProofs/FormalGroupPointsHomDef.lean#L1151-L1211

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

theorem Formalism.ELL.FormalGroupPointsHom.e1hom_main (hU : WSubstUnique.{u}) (hS : WChordSubst.{u}) (hPar : FormalGroupPointsParametrisation.{u})
    {W : WeierstrassCurve K} {w : PowerSeries K} (hW : IntegralModel W) (hw : WFixed W w)
    (F : FormalGroup K) (hFi : IntegralMv F.toPowerSeries)
    (hch : ChordAt W w (MvPowerSeries.X 0) (MvPowerSeries.X 1) F.toPowerSeries)
    {inst : DecidableEq K} (P Q : W.toAffine.Point) (hP : InFormalGroupPoints P) (hQ : InFormalGroupPoints Q) :
    uOf (P + Q) = evalMv2 F.toPowerSeries (uOf P) (uOf Q) := by sorry
