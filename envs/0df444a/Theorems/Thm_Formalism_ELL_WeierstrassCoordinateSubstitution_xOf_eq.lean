-- Prove2me | Theorems.Thm_Formalism_ELL_WeierstrassCoordinateSubstitution_xOf_eq
-- name    : Formalism.ELL.WeierstrassCoordinateSubstitution.xOf_eq
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T18:22:12.60283+00:00
-- url     : https://prove2.me/theorems/fc625c0d-4141-4977-a7e2-012cfe945673
-- title:
--   Weierstrass Coordinate Substitution: x Of eq
-- statement:
--   The Weierstrass Coordinate Substitution construction uses the x Of eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/EllipticTorsion/EllipticTorsionProofs/ExistsUnitFactor.lean#L55-L65
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/EllipticTorsion/EllipticTorsionProofs/ExistsUnitFactor.lean#L55-L65

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

theorem Formalism.ELL.WeierstrassCoordinateSubstitution.xOf_eq {u w : PowerSeries K} (hwu : w = X ^ 3 * u) (hu : constantCoeff u = 1)
    {σ : Type} (s : MvPowerSeries σ K) (hs : MvPowerSeries.constantCoeff s = 0) (hne : s ≠ 0) :
    xOf w s = (algebraMap (MvPowerSeries σ K) (FractionRing (MvPowerSeries σ K))
      (s ^ 2 * u.subst s))⁻¹ := by sorry
