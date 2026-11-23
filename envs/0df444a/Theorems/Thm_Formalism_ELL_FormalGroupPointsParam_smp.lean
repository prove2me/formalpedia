-- Prove2me | Theorems.Thm_Formalism_ELL_FormalGroupPointsParam_smp
-- name    : Formalism.ELL.FormalGroupPointsParam.smp
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T02:15:16.199023+00:00
-- url     : https://prove2.me/theorems/da135657-eec0-4b1b-a71d-49214fd43c99
-- title:
--   Formal Group Points Param: smp
-- statement:
--   The Formal Group Points Param construction uses the smp property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/EllipticTorsion/EllipticTorsionProofs/FormalGroupPointsParamDef.lean#L121-L122
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/EllipticTorsion/EllipticTorsionProofs/FormalGroupPointsParamDef.lean#L121-L122

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

theorem Formalism.ELL.FormalGroupPointsParam.smp {a b : K} (ha : ‖a‖ < 1) (hb : ‖b‖ < 1) : ‖a * b‖ < 1 := by sorry
