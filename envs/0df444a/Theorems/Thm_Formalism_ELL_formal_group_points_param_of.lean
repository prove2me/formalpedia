-- Prove2me | Theorems.Thm_Formalism_ELL_formal_group_points_param_of
-- name    : Formalism.ELL.formal_group_points_param_of
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T18:27:15.137385+00:00
-- url     : https://prove2.me/theorems/a8c7972f-5ca3-47fb-b8f9-f1b2406a7292
-- title:
--   ELL: formal group points param of
-- statement:
--   The ELL construction uses the formal group points param of property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/EllipticTorsion/EllipticTorsionProofs/FormalGroupPointsParamDef.lean#L331-L331
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/EllipticTorsion/EllipticTorsionProofs/FormalGroupPointsParamDef.lean#L331-L331

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

theorem Formalism.ELL.formal_group_points_param_of (_hU : WSubstUnique.{u}) : FormalGroupPointsParametrisation.{u} := by sorry
