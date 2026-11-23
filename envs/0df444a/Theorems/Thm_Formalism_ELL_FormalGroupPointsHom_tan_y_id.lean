-- Prove2me | Theorems.Thm_Formalism_ELL_FormalGroupPointsHom_tan_y_id
-- name    : Formalism.ELL.FormalGroupPointsHom.tan_y_id
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T18:10:35.038706+00:00
-- url     : https://prove2.me/theorems/a66366bd-addf-47d8-8ccb-8239b82b3938
-- title:
--   Formal Group Points Hom: tan y id
-- statement:
--   The Formal Group Points Hom construction uses the tan y id property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/EllipticTorsion/EllipticTorsionProofs/FormalGroupPointsHomDef.lean#L424-L432
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/EllipticTorsion/EllipticTorsionProofs/FormalGroupPointsHomDef.lean#L424-L432

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

theorem Formalism.ELL.FormalGroupPointsHom.tan_y_id {z w c v : E} (hw : w ≠ 0) (hM : -2 + W.a₁ * z + W.a₃ * w ≠ 0) (hv : v ≠ 0) :
    (-1 / v - W.negY (c / v) ((3 * (z / w) ^ 2 + 2 * W.a₂ * (z / w) + W.a₄ - W.a₁ * (-1 / w)) /
      (-1 / w - W.negY (z / w) (-1 / w)) * (c / v - z / w) + -1 / w))
      * (v * w ^ 2 * (-2 + W.a₁ * z + W.a₃ * w)) = - tanPY W.a₁ W.a₂ W.a₃ W.a₄ z w c v := by sorry
