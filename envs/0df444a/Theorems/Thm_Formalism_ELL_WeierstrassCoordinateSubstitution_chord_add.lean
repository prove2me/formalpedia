-- Prove2me | Theorems.Thm_Formalism_ELL_WeierstrassCoordinateSubstitution_chord_add
-- name    : Formalism.ELL.WeierstrassCoordinateSubstitution.chord_add
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T02:14:13.557175+00:00
-- url     : https://prove2.me/theorems/4ba64fcc-5ad6-4cbc-b053-d5705fd8e4c2
-- title:
--   Weierstrass Coordinate Substitution: chord add
-- statement:
--   The Weierstrass Coordinate Substitution construction uses the chord add property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/EllipticTorsion/EllipticTorsionProofs/ExistsUnitFactor.lean#L124-L141
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/EllipticTorsion/EllipticTorsionProofs/ExistsUnitFactor.lean#L124-L141

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

theorem Formalism.ELL.WeierstrassCoordinateSubstitution.chord_add {W : WeierstrassCurve K} {w : PowerSeries K} {σ : Type}
    [DecidableEq (FractionRing (MvPowerSeries σ K))] (s t r : MvPowerSeries σ K)
    (hs : (W.map (algebraMap K (FractionRing (MvPowerSeries σ K)))).toAffine.Nonsingular
      (xOf w s) (yOf w s))
    (ht : (W.map (algebraMap K (FractionRing (MvPowerSeries σ K)))).toAffine.Nonsingular
      (xOf w t) (yOf w t))
    (hne : xOf w s ≠ xOf w t) (hch : ChordAt W w s t r) :
    ∃ h : (W.map (algebraMap K (FractionRing (MvPowerSeries σ K)))).toAffine.Nonsingular
      (xOf w r) (yOf w r),
      WeierstrassCurve.Affine.Point.some _ _ hs + WeierstrassCurve.Affine.Point.some _ _ ht =
        WeierstrassCurve.Affine.Point.some _ _ h := by sorry
