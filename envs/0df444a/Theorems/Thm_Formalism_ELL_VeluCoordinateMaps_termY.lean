-- Prove2me | Theorems.Thm_Formalism_ELL_VeluCoordinateMaps_termY
-- name    : Formalism.ELL.VeluCoordinateMaps.termY
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T18:19:12.562798+00:00
-- url     : https://prove2.me/theorems/767935e2-fff1-46f8-9f21-6beae71a6ec7
-- title:
--   Velu Coordinate Maps: term Y
-- statement:
--   The Velu Coordinate Maps construction uses the term Y property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/EllipticTorsion/EllipticTorsionProofs/VeluUSeries.lean#L86-L94
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/EllipticTorsion/EllipticTorsionProofs/VeluUSeries.lean#L86-L94

import Definitions.Def_Formalism_EllipticTorsion_VeluIntegralModel
import Definitions.Def_Formalism_EllipticTorsion_EllipticTorsionProofs_WPoint
import Definitions.Def_Formalism_EllipticTorsion_EllipticTorsionProofs_FormalGroupPointsParamDef
import Definitions.Def_Formalism_EllipticTorsion_EllipticTorsionProofs_VeluUSeries
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
open Formalism.ELL.VeluCoordinateMaps
open Formalism.G
variable {F : Type*} [Field F]

theorem Formalism.ELL.VeluCoordinateMaps.termY (x y xQ yQ u Di Ui v uQ c a1 a3 : F) (h : (x - xQ)⁻¹ = u ^ 2 * Di)
    (hx : x * u ^ 2 = Ui) (hy : y * u ^ 3 = -Ui) :
    (uQ * (2 * y + a1 * x + a3) / (x - xQ) ^ 3 + v * (a1 * (x - xQ) + y - yQ) / (x - xQ) ^ 2
        + c / (x - xQ) ^ 2) * u ^ 3 =
      u ^ 4 * (uQ * (-2 * Ui * u ^ 2 + a1 * Ui * u ^ 3 + a3 * u ^ 5) * Di ^ 3
        + v * (a1 * (Ui - xQ * u ^ 2) * u - Ui - yQ * u ^ 3) * Di ^ 2 + c * u ^ 3 * Di ^ 2) := by sorry
