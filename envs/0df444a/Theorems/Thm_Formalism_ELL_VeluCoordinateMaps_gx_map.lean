-- Prove2me | Theorems.Thm_Formalism_ELL_VeluCoordinateMaps_gx_map
-- name    : Formalism.ELL.VeluCoordinateMaps.gx_map
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T02:18:20.701825+00:00
-- url     : https://prove2.me/theorems/187ed48d-9a1b-4abf-856c-e8ff8579e564
-- title:
--   Velu Coordinate Maps: gx map
-- statement:
--   The Velu Coordinate Maps construction uses the gx map property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/EllipticTorsion/EllipticTorsionProofs/VeluUSeries.lean#L21-L22
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/EllipticTorsion/EllipticTorsionProofs/VeluUSeries.lean#L21-L22

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
variable {K L : Type*} [Field K] [Field L] (f : K →+* L) (W : WeierstrassCurve K) (a b : K)

theorem Formalism.ELL.VeluCoordinateMaps.gx_map : veluGx (W.map f) (f a) (f b) = f (veluGx W a b) := by sorry
