-- Prove2me | Theorems.Thm_Formalism_ELL_FormalGroupPointsParam_ev_C
-- name    : Formalism.ELL.FormalGroupPointsParam.ev_C
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T02:20:13.586403+00:00
-- url     : https://prove2.me/theorems/2955d885-fc67-42b3-811d-d45fc2cda6ff
-- title:
--   Formal Group Points Param: ev C
-- statement:
--   The Formal Group Points Param construction uses the ev C property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/EllipticTorsion/EllipticTorsionProofs/FormalGroupPointsParamDef.lean#L24-L34
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/EllipticTorsion/EllipticTorsionProofs/FormalGroupPointsParamDef.lean#L24-L34

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
variable {K : Type u} [NormedField K]

theorem Formalism.ELL.FormalGroupPointsParam.ev_C (a t : K) : Ev (C a) t a := by sorry
