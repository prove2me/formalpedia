-- Prove2me | Theorems.Thm_Formalism_L2_G_Cmp_mem_spanK
-- name    : Formalism.L2.G.Cmp.mem_spanK
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T07:54:29.912536+00:00
-- url     : https://prove2.me/theorems/16a449ab-30d5-4737-88e9-a80d0fab5159
-- title:
--   Cmp: mem span K
-- statement:
--   The Cmp construction uses the mem span K property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/GroupLattices/ComparisonMaps/IsComplRatCompl.lean#L13-L13
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/GroupLattices/ComparisonMaps/IsComplRatCompl.lean#L13-L13

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_GroupLattices_ComparisonMaps_IsComplRatCompl
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism Formalism.L2 Formalism.L2.G Formalism.L2.G.Cmp
variable {LL Kf : Type*} [Field LL] [Field Kf] {e : LL →+* Kf}
  {V0 V1 W0 W1 ι : Type*} [AddCommGroup V0] [Module LL V0] [AddCommGroup V1] [Module LL V1]
  [AddCommGroup W0] [Module Kf W0] [AddCommGroup W1] [Module Kf W1]

theorem Formalism.L2.G.Cmp.mem_spanK (c0 : V0 →ₛₗ[e] W0) (x : V0) : c0 x ∈ spanK c0 := by sorry
