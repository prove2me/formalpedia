-- Prove2me | Theorems.Thm_Formalism_ELL_WeierstrassCoordinateSubstitution_assoc_of
-- name    : Formalism.ELL.WeierstrassCoordinateSubstitution.assoc_of
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T02:20:46.704004+00:00
-- url     : https://prove2.me/theorems/bdaac9c3-a1c5-40f3-8031-ca2d5a515b97
-- title:
--   Weierstrass Coordinate Substitution: assoc of
-- statement:
--   The Weierstrass Coordinate Substitution construction uses the assoc of property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/EllipticTorsion/EllipticTorsionProofs/ExistsUnitFactor.lean#L181-L271
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/EllipticTorsion/EllipticTorsionProofs/ExistsUnitFactor.lean#L181-L271

import Definitions.Def_Formalism_EllipticTorsion_WChordSeries
import Definitions.Def_Formalism_EllipticTorsion_EllipticTorsionProofs_ExistsUnitFactor
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
open Formalism Formalism.ELL
open Formalism.ELL.WeierstrassCoordinateSubstitution
variable {K : Type u} [Field K]

theorem Formalism.ELL.WeierstrassCoordinateSubstitution.assoc_of (hS : WChordSubst.{u}) (hP : WPoint.{u}) {W : WeierstrassCurve K}
    {w : PowerSeries K} (hw : WFixed W w) {u : PowerSeries K} (hwu : w = X ^ 3 * u)
    (hu : constantCoeff u = 1) (F : MvPowerSeries (Fin 2) K)
    (hF0 : MvPowerSeries.constantCoeff F = 0)
    (hF1 : MvPowerSeries.coeff (Finsupp.single 0 1) F = 1)
    (hch : ChordAt W w (MvPowerSeries.X 0) (MvPowerSeries.X 1) F) :
    F.subst ![F.subst ![(MvPowerSeries.X 0 : MvPowerSeries (Fin 3) K), MvPowerSeries.X 1],
        MvPowerSeries.X 2] =
      F.subst ![(MvPowerSeries.X 0 : MvPowerSeries (Fin 3) K),
        F.subst ![(MvPowerSeries.X 1 : MvPowerSeries (Fin 3) K), MvPowerSeries.X 2]] := by sorry
