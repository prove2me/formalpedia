-- Prove2me | Theorems.Thm_Formalism_ELL_VeluCoordinateMaps_c_mem
-- name    : Formalism.ELL.VeluCoordinateMaps.c_mem
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T18:19:22.401089+00:00
-- url     : https://prove2.me/theorems/74642557-43d6-492c-9e1d-2a198085439c
-- title:
--   Velu Coordinate Maps: c mem
-- statement:
--   The Velu Coordinate Maps construction uses the c mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/EllipticTorsion/EllipticTorsionProofs/VeluUSeries.lean#L72-L73
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/EllipticTorsion/EllipticTorsionProofs/VeluUSeries.lean#L72-L73

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
variable {K : Type u} [NormedField K] [IsUltrametricDist K]
variable {W : WeierstrassCurve K} (hW : IntegralModel W) {a b : K} (ha : ‖a‖ ≤ 1) (hb : ‖b‖ ≤ 1)
include hW ha hb

theorem Formalism.ELL.VeluCoordinateMaps.c_mem : W.a₁ * veluU W a b - veluGx W a b * veluGy W a b ∈ unitBall K := by sorry
