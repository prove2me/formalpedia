-- Prove2me | Theorems.Thm_Formalism_ELL_FormalGroupPointsParam_smm
-- name    : Formalism.ELL.FormalGroupPointsParam.smm
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T02:04:21.792289+00:00
-- url     : https://prove2.me/theorems/77b6cc6b-0ce5-4d0b-b49b-0c691b8912d4
-- title:
--   Formal Group Points Param: smm
-- statement:
--   The Formal Group Points Param construction uses the smm property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/EllipticTorsion/EllipticTorsionProofs/FormalGroupPointsParamDef.lean#L117-L119
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/EllipticTorsion/EllipticTorsionProofs/FormalGroupPointsParamDef.lean#L117-L119

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

theorem Formalism.ELL.FormalGroupPointsParam.smm {c a : K} (hc : ‖c‖ ≤ 1) (ha : ‖a‖ < 1) : ‖c * a‖ < 1 := by sorry
