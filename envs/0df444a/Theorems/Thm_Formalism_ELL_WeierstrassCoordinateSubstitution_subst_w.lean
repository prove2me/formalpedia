-- Prove2me | Theorems.Thm_Formalism_ELL_WeierstrassCoordinateSubstitution_subst_w
-- name    : Formalism.ELL.WeierstrassCoordinateSubstitution.subst_w
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T02:11:49.746935+00:00
-- url     : https://prove2.me/theorems/8008fcc3-8ae9-4123-a8cf-0e4d5684bf0e
-- title:
--   Weierstrass Coordinate Substitution: subst w
-- statement:
--   The Weierstrass Coordinate Substitution construction uses the subst w property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/EllipticTorsion/EllipticTorsionProofs/ExistsUnitFactor.lean#L39-L43
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/EllipticTorsion/EllipticTorsionProofs/ExistsUnitFactor.lean#L39-L43

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

theorem Formalism.ELL.WeierstrassCoordinateSubstitution.subst_w {u w : PowerSeries K} (hwu : w = X ^ 3 * u) {σ : Type}
    (s : MvPowerSeries σ K) (hs : MvPowerSeries.constantCoeff s = 0) :
    w.subst s = s ^ 3 * u.subst s := by sorry
