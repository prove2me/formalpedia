-- Prove2me | Theorems.Thm_Formalism_ELL_WeierstrassCoordinateSubstitution_isUnit_subst
-- name    : Formalism.ELL.WeierstrassCoordinateSubstitution.isUnit_subst
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T02:01:42.875129+00:00
-- url     : https://prove2.me/theorems/5461badb-8e70-4a83-bf77-2efd040bdb01
-- title:
--   Weierstrass Coordinate Substitution: is Unit subst
-- statement:
--   The Weierstrass Coordinate Substitution construction uses the is Unit subst property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/EllipticTorsion/EllipticTorsionProofs/ExistsUnitFactor.lean#L45-L53
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/EllipticTorsion/EllipticTorsionProofs/ExistsUnitFactor.lean#L45-L53

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

theorem Formalism.ELL.WeierstrassCoordinateSubstitution.isUnit_subst {u : PowerSeries K} (hu : constantCoeff u = 1) {σ : Type}
    (s : MvPowerSeries σ K) (hs : MvPowerSeries.constantCoeff s = 0) :
    IsUnit (u.subst s) := by sorry
