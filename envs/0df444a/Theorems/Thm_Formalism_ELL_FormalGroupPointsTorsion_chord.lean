-- Prove2me | Theorems.Thm_Formalism_ELL_FormalGroupPointsTorsion_chord
-- name    : Formalism.ELL.FormalGroupPointsTorsion.chord
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T02:31:34.187274+00:00
-- url     : https://prove2.me/theorems/0ce6d574-21b6-45f7-9e13-b7a04057371f
-- title:
--   Formal Group Points Torsion: chord
-- statement:
--   The Formal Group Points Torsion construction uses the chord property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/EllipticTorsion/EllipticTorsionProofs/FormalGroupPointsNoPrimeToPTorsion.lean#L307-L364
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/EllipticTorsion/EllipticTorsionProofs/FormalGroupPointsNoPrimeToPTorsion.lean#L307-L364

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

theorem Formalism.ELL.FormalGroupPointsTorsion.chord [DecidableEq K] (hW : IntegralModel W) {x1 x2 y1 y2 : K}
    (h1 : W.toAffine.Equation x1 y1) (h2 : W.toAffine.Equation x2 y2)
    (hX1 : 1 < ‖x1‖) (hX2 : 1 < ‖x2‖) (hxy : ¬(x1 = x2 ∧ y1 = W.toAffine.negY x2 y2)) :
    1 < ‖W.toAffine.addX x1 x2 (W.toAffine.slope x1 x2 y1 y2)‖ ∧
    ‖W.toAffine.addX x1 x2 (W.toAffine.slope x1 x2 y1 y2) /
        W.toAffine.addY x1 x2 y1 (W.toAffine.slope x1 x2 y1 y2) - x1 / y1 - x2 / y2‖ <
      max ‖x1 / y1‖ ‖x2 / y2‖ := by sorry
