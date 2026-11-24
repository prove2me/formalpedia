-- Prove2me | Theorems.Thm_Formalism_L2_G_isSquare_algebraMap
-- name    : Formalism.L2.G.isSquare_algebraMap
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T07:56:21.45254+00:00
-- url     : https://prove2.me/theorems/57ee487e-8056-4b46-a196-e43f56ba703b
-- title:
--   G: is Square algebra Map
-- statement:
--   The G construction uses the is Square algebra Map property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/GroupLattices/PerfectRings/ExistsSqEqIntCast.lean#L397-L417
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/GroupLattices/PerfectRings/ExistsSqEqIntCast.lean#L397-L417

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_GroupLattices_PerfectRings_ExistsSqEqIntCast
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Polynomial
noncomputable section
open Formalism Formalism.L2 Formalism.L2.G
variable (p : ℕ) [hp : Fact p.Prime] (n : ℕ) [NeZero n]

theorem Formalism.L2.G.isSquare_algebraMap (hp2 : p ≠ 2) (a : F1 p n) : IsSquare (algebraMap (F1 p n) (F2 p n) a) := by sorry
