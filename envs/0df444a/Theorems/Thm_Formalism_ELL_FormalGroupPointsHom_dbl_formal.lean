-- Prove2me | Theorems.Thm_Formalism_ELL_FormalGroupPointsHom_dbl_formal
-- name    : Formalism.ELL.FormalGroupPointsHom.dbl_formal
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T18:10:23.598237+00:00
-- url     : https://prove2.me/theorems/fd859086-11d0-47f9-a3f5-0019e1c93398
-- title:
--   Formal Group Points Hom: dbl formal
-- statement:
--   The Formal Group Points Hom construction uses the dbl formal property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/EllipticTorsion/EllipticTorsionProofs/FormalGroupPointsHomDef.lean#L699-L804
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/EllipticTorsion/EllipticTorsionProofs/FormalGroupPointsHomDef.lean#L699-L804

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
variable {K : Type u} [Field K]

theorem Formalism.ELL.FormalGroupPointsHom.dbl_formal (hU : WSubstUnique.{u}) (hS : WChordSubst.{u}) {W : WeierstrassCurve K}
    {w : PowerSeries K} (hw : WFixed W w) (F : FormalGroup K)
    (hch : ChordAt W w (MvPowerSeries.X 0) (MvPowerSeries.X 1) F.toPowerSeries)
    (hy : yOf w (MvPowerSeries.X 0 : MvPowerSeries (Fin 2) K) ≠
      (W.map (algebraMap K (FractionRing (MvPowerSeries (Fin 2) K)))).toAffine.negY
        (xOf w (MvPowerSeries.X 0 : MvPowerSeries (Fin 2) K))
        (yOf w (MvPowerSeries.X 0 : MvPowerSeries (Fin 2) K))) :
    F.toPowerSeries.subst ![(MvPowerSeries.X 0 : MvPowerSeries (Fin 2) K), MvPowerSeries.X 0] ≠ 0 ∧
    xOf w (F.toPowerSeries.subst ![(MvPowerSeries.X 0 : MvPowerSeries (Fin 2) K), MvPowerSeries.X 0]) =
      (W.map (algebraMap K (FractionRing (MvPowerSeries (Fin 2) K)))).toAffine.addX
        (xOf w (MvPowerSeries.X 0 : MvPowerSeries (Fin 2) K))
        (xOf w (MvPowerSeries.X 0 : MvPowerSeries (Fin 2) K))
        ((3 * (xOf w (MvPowerSeries.X 0 : MvPowerSeries (Fin 2) K)) ^ 2
          + 2 * (W.map (algebraMap K (FractionRing (MvPowerSeries (Fin 2) K)))).toAffine.a₂
            * (xOf w (MvPowerSeries.X 0 : MvPowerSeries (Fin 2) K))
          + (W.map (algebraMap K (FractionRing (MvPowerSeries (Fin 2) K)))).toAffine.a₄
          - (W.map (algebraMap K (FractionRing (MvPowerSeries (Fin 2) K)))).toAffine.a₁
            * (yOf w (MvPowerSeries.X 0 : MvPowerSeries (Fin 2) K))) /
          (yOf w (MvPowerSeries.X 0 : MvPowerSeries (Fin 2) K) -
            (W.map (algebraMap K (FractionRing (MvPowerSeries (Fin 2) K)))).toAffine.negY
              (xOf w (MvPowerSeries.X 0 : MvPowerSeries (Fin 2) K))
              (yOf w (MvPowerSeries.X 0 : MvPowerSeries (Fin 2) K)))) ∧
    yOf w (F.toPowerSeries.subst ![(MvPowerSeries.X 0 : MvPowerSeries (Fin 2) K), MvPowerSeries.X 0]) =
      (W.map (algebraMap K (FractionRing (MvPowerSeries (Fin 2) K)))).toAffine.addY
        (xOf w (MvPowerSeries.X 0 : MvPowerSeries (Fin 2) K))
        (xOf w (MvPowerSeries.X 0 : MvPowerSeries (Fin 2) K))
        (yOf w (MvPowerSeries.X 0 : MvPowerSeries (Fin 2) K))
        ((3 * (xOf w (MvPowerSeries.X 0 : MvPowerSeries (Fin 2) K)) ^ 2
          + 2 * (W.map (algebraMap K (FractionRing (MvPowerSeries (Fin 2) K)))).toAffine.a₂
            * (xOf w (MvPowerSeries.X 0 : MvPowerSeries (Fin 2) K))
          + (W.map (algebraMap K (FractionRing (MvPowerSeries (Fin 2) K)))).toAffine.a₄
          - (W.map (algebraMap K (FractionRing (MvPowerSeries (Fin 2) K)))).toAffine.a₁
            * (yOf w (MvPowerSeries.X 0 : MvPowerSeries (Fin 2) K))) /
          (yOf w (MvPowerSeries.X 0 : MvPowerSeries (Fin 2) K) -
            (W.map (algebraMap K (FractionRing (MvPowerSeries (Fin 2) K)))).toAffine.negY
              (xOf w (MvPowerSeries.X 0 : MvPowerSeries (Fin 2) K))
              (yOf w (MvPowerSeries.X 0 : MvPowerSeries (Fin 2) K)))) := by sorry
