-- Prove2me | Theorems.Thm_Formalism_ELL_FormalGroupPointsParam_norm_three_le
-- name    : Formalism.ELL.FormalGroupPointsParam.norm_three_le
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T02:18:01.228023+00:00
-- url     : https://prove2.me/theorems/890a6e7f-d9dc-4da4-a89f-22634c4559fd
-- title:
--   Formal Group Points Param: norm three le
-- statement:
--   The Formal Group Points Param construction uses the norm three le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/EllipticTorsion/EllipticTorsionProofs/FormalGroupPointsParamDef.lean#L130-L131
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/EllipticTorsion/EllipticTorsionProofs/FormalGroupPointsParamDef.lean#L130-L131

import Definitions.Def_Formalism_EllipticTorsion_FormalGroupPointsParametrisation
import Definitions.Def_Formalism_EllipticTorsion_EllipticTorsionProofs_WSeries
import Definitions.Def_Formalism_EllipticTorsion_EllipticTorsionProofs_FormalGroupPointsParamDef
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
open Formalism.ELL.FormalGroupPointsParam
open Formalism.G
variable {K : Type u} [NormedField K] [IsUltrametricDist K]

theorem Formalism.ELL.FormalGroupPointsParam.norm_three_le : ‖(3 : K)‖ ≤ 1 := by sorry
