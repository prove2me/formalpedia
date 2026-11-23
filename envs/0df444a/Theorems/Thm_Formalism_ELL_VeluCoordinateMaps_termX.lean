-- Prove2me | Theorems.Thm_Formalism_ELL_VeluCoordinateMaps_termX
-- name    : Formalism.ELL.VeluCoordinateMaps.termX
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T18:18:51.230304+00:00
-- url     : https://prove2.me/theorems/1c049921-ca02-488a-b26d-f388a5283246
-- title:
--   Velu Coordinate Maps: term X
-- statement:
--   The Velu Coordinate Maps construction uses the term X property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/EllipticTorsion/EllipticTorsionProofs/VeluUSeries.lean#L81-L84
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/EllipticTorsion/EllipticTorsionProofs/VeluUSeries.lean#L81-L84

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

theorem Formalism.ELL.VeluCoordinateMaps.termX (x xQ u Di v uQ : F) (h : (x - xQ)⁻¹ = u ^ 2 * Di) :
    (v / (x - xQ) + uQ / (x - xQ) ^ 2) * u ^ 2 = u ^ 4 * (v * Di + uQ * u ^ 2 * Di ^ 2) := by sorry
