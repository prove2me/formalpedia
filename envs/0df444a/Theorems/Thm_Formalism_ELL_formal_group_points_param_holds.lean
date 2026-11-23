-- Prove2me | Theorems.Thm_Formalism_ELL_formal_group_points_param_holds
-- name    : Formalism.ELL.formal_group_points_param_holds
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T18:27:28.159588+00:00
-- url     : https://prove2.me/theorems/d0eb0041-ff5d-4255-a815-c8578ca6e6bb
-- title:
--   ELL: formal group points param holds
-- statement:
--   The ELL construction uses the formal group points param holds property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/EllipticTorsion/EllipticTorsionProofs/FormalGroupPointsParamDef.lean#L200-L329
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/EllipticTorsion/EllipticTorsionProofs/FormalGroupPointsParamDef.lean#L200-L329

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
open FormalGroupPointsParam

theorem Formalism.ELL.formal_group_points_param_holds : FormalGroupPointsParametrisation.{u} := by sorry
