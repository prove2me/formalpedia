-- Prove2me | Theorems.Thm_Formalism_ELL_FormalGroupPointsSubgroup_le_sub_of_lt
-- name    : Formalism.ELL.FormalGroupPointsSubgroup.le_sub_of_lt
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T02:00:37.944395+00:00
-- url     : https://prove2.me/theorems/488d4f2c-4e59-4539-a9db-5c0e002310fe
-- title:
--   Formal Group Points Subgroup: le sub of lt
-- statement:
--   The Formal Group Points Subgroup construction uses the le sub of lt property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/EllipticTorsion/EllipticTorsionProofs/FormalGroupPointsSubgroupHolds.lean#L21-L26
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/EllipticTorsion/EllipticTorsionProofs/FormalGroupPointsSubgroupHolds.lean#L21-L26

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
open Formalism Formalism.ELL Formalism.ELL.FormalGroupPointsSubgroup
open WeierstrassCurve Polynomial
variable {K : Type u} [NormedField K] [IsUltrametricDist K]

theorem Formalism.ELL.FormalGroupPointsSubgroup.le_sub_of_lt {a b : K} (h : ‖b‖ < ‖a‖) : ‖a‖ ≤ ‖a - b‖ := by sorry
