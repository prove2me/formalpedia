-- Prove2me | Theorems.Thm_Formalism_ELL_TorsionIntegralEllipticTorsion_y_int
-- name    : Formalism.ELL.TorsionIntegralEllipticTorsion.y_int
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T18:18:55.426257+00:00
-- url     : https://prove2.me/theorems/c55102c3-236a-4e77-9118-4ed6114005d1
-- title:
--   Torsion Integral Elliptic Torsion: y int
-- statement:
--   The Torsion Integral Elliptic Torsion construction uses the y int property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/EllipticTorsion/EllipticTorsionProofs/TorInt.lean#L12-L62
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/EllipticTorsion/EllipticTorsionProofs/TorInt.lean#L12-L62

import Mathlib
import Definitions.Def_Formalism_EllipticTorsion_FormalGroupPointsTorsionFree
import Definitions.Def_Formalism_EllipticTorsion_EllipticTorsionProofs_TorInt
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
universe u
noncomputable section
open Formalism Formalism.ELL Formalism.ELL.TorsionIntegralEllipticTorsion
open WeierstrassCurve Formalism.ELL

theorem Formalism.ELL.TorsionIntegralEllipticTorsion.y_int {K : Type u} [NormedField K] [IsUltrametricDist K] (W : WeierstrassCurve K)
    (hW : IntegralModel W) {x y : K} (h : W.toAffine.Equation x y) (hx : ‖x‖ ≤ 1) :
    ‖y‖ ≤ 1 := by sorry
