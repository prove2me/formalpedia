-- Prove2me | Theorems.Thm_Formalism_ELL_FormalGroupPointsHom_tan_slope
-- name    : Formalism.ELL.FormalGroupPointsHom.tan_slope
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T02:28:04.356712+00:00
-- url     : https://prove2.me/theorems/0b9ecfe0-12cb-47f0-ac94-3c8281d8f188
-- title:
--   Formal Group Points Hom: tan slope
-- statement:
--   The Formal Group Points Hom construction uses the tan slope property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/EllipticTorsion/EllipticTorsionProofs/FormalGroupPointsHomDef.lean#L404-L412
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/EllipticTorsion/EllipticTorsionProofs/FormalGroupPointsHomDef.lean#L404-L412

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
variable {E : Type*} [Field E] (W : WeierstrassCurve.Affine E)

theorem Formalism.ELL.FormalGroupPointsHom.tan_slope {z w : E} (hw : w ≠ 0) (hM : -2 + W.a₁ * z + W.a₃ * w ≠ 0) :
    (3 * (z / w) ^ 2 + 2 * W.a₂ * (z / w) + W.a₄ - W.a₁ * (-1 / w)) /
      (-1 / w - W.negY (z / w) (-1 / w)) =
    (3 * z ^ 2 + 2 * W.a₂ * z * w + W.a₄ * w ^ 2 + W.a₁ * w) / (w * (-2 + W.a₁ * z + W.a₃ * w)) := by sorry
