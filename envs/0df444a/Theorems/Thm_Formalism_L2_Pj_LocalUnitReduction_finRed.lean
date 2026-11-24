-- Prove2me | Theorems.Thm_Formalism_L2_Pj_LocalUnitReduction_finRed
-- name    : Formalism.L2.Pj.LocalUnitReduction.finRed
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T08:38:16.656356+00:00
-- url     : https://prove2.me/theorems/39b980d6-c158-4749-8e66-171133213980
-- title:
--   Local Unit Reduction: fin Red
-- statement:
--   The Local Unit Reduction construction uses the fin Red property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/ProjectiveLattices/LocalUnitReduction/IsUnitMkOfForallPrime.lean#L128-L143
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/ProjectiveLattices/LocalUnitReduction/IsUnitMkOfForallPrime.lean#L128-L143

import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_LocalUnitReduction_FinRedStatement
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_LocalUnitReduction_IsUnitMkOfForallPrime
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.L2 Formalism.L2.Pj Formalism.L2.Pj.LocalUnitReduction

theorem Formalism.L2.Pj.LocalUnitReduction.finRed : FinRedStatement := by sorry
