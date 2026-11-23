-- Prove2me | Theorems.Thm_Formalism_ELL_FormalGroupPointsTorsion_zfacts
-- name    : Formalism.ELL.FormalGroupPointsTorsion.zfacts
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T02:01:14.520586+00:00
-- url     : https://prove2.me/theorems/3b3cf330-268d-4012-b03b-275d00557188
-- title:
--   Formal Group Points Torsion: zfacts
-- statement:
--   The Formal Group Points Torsion construction uses the zfacts property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/EllipticTorsion/EllipticTorsionProofs/FormalGroupPointsNoPrimeToPTorsion.lean#L75-L85
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/EllipticTorsion/EllipticTorsionProofs/FormalGroupPointsNoPrimeToPTorsion.lean#L75-L85

import Mathlib
import Definitions.Def_Formalism_EllipticTorsion_FormalGroupPointsTorsionFree
import Definitions.Def_Formalism_EllipticTorsion_EllipticTorsionProofs_FormalGroupPointsNoPrimeToPTorsion
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
universe u
open Formalism Formalism.ELL Formalism.ELL.FormalGroupPointsTorsion
open WeierstrassCurve Polynomial
variable {K : Type u} [NormedField K] [IsUltrametricDist K]
variable {W : WeierstrassCurve K}

theorem Formalism.ELL.FormalGroupPointsTorsion.zfacts (hW : IntegralModel W) {x y : K} (h : W.toAffine.Equation x y) (hx : 1 < ‖x‖) :
    y ≠ 0 ∧ 0 < ‖x / y‖ ∧ ‖x / y‖ < 1 ∧ ‖x / y‖ ^ 2 * ‖x‖ = 1 := by sorry
