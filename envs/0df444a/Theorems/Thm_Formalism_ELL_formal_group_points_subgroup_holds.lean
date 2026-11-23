-- Prove2me | Theorems.Thm_Formalism_ELL_formal_group_points_subgroup_holds
-- name    : Formalism.ELL.formal_group_points_subgroup_holds
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T18:27:30.422218+00:00
-- url     : https://prove2.me/theorems/dbdb5454-c54b-4146-afe7-0fedc69942e3
-- title:
--   ELL: formal group points subgroup holds
-- statement:
--   The ELL construction uses the formal group points subgroup holds property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/EllipticTorsion/EllipticTorsionProofs/FormalGroupPointsSubgroupHolds.lean#L180-L194
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/EllipticTorsion/EllipticTorsionProofs/FormalGroupPointsSubgroupHolds.lean#L180-L194

import Mathlib
import Definitions.Def_Formalism_EllipticTorsion_FormalGroupPointsTorsionFree
import Definitions.Def_Formalism_EllipticTorsion_EllipticTorsionProofs_FormalGroupPointsSubgroupHolds
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
universe u
open Formalism Formalism.ELL
open WeierstrassCurve
open Classical

theorem Formalism.ELL.formal_group_points_subgroup_holds : Formalism.ELL.FormalGroupPointsSubgroup' := by sorry
