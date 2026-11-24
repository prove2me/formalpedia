-- Prove2me | Theorems.Thm_Formalism_HF_Final_hostDensityArith
-- name    : Formalism.HF.Final.hostDensityArith
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T06:24:14.869796+00:00
-- url     : https://prove2.me/theorems/3f74f019-a31c-4083-8d2e-b6651b68f59f
-- title:
--   Final: host Density Arith
-- statement:
--   The Final construction uses the host Density Arith property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/DirichletDensity/HostDensityArith.lean#L15-L15
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/DirichletDensity/HostDensityArith.lean#L15-L15

import Definitions.Def_Formalism_DirichletDensity_DirichletDensityProofs_QuadDiscr
import Definitions.Def_Formalism_DirichletDensity_DirichletDensityProofs_MQDiscr
import Definitions.Def_Formalism_DirichletDensity_DirichletDensityProofs_APLogDensity
import Definitions.Def_Formalism_DirichletDensity_DirichletDensityProofs_LogToDir
import Definitions.Def_Formalism_DirichletDensity_DirichletDensityProofs_HostDensityArith
import Definitions.Def_Formalism_DirichletDensity_DirichletDensityProofs_HostDensity
import Definitions.Def_Formalism_DirichletDensity_HostDensityArith
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.HF Formalism.HF.Final

theorem Formalism.HF.Final.hostDensityArith : Formalism.HF.HostDensityArith := by sorry
