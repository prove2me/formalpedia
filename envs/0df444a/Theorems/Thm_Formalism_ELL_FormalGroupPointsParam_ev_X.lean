-- Prove2me | Theorems.Thm_Formalism_ELL_FormalGroupPointsParam_ev_X
-- name    : Formalism.ELL.FormalGroupPointsParam.ev_X
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T18:10:30.738888+00:00
-- url     : https://prove2.me/theorems/77b15fb1-d4cb-4f90-a352-d067c5d318bf
-- title:
--   Formal Group Points Param: ev X
-- statement:
--   The Formal Group Points Param construction uses the ev X property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/EllipticTorsion/EllipticTorsionProofs/FormalGroupPointsParamDef.lean#L36-L46
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/EllipticTorsion/EllipticTorsionProofs/FormalGroupPointsParamDef.lean#L36-L46

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

theorem Formalism.ELL.FormalGroupPointsParam.ev_X (t : K) : Ev (X : PowerSeries K) t t := by sorry
