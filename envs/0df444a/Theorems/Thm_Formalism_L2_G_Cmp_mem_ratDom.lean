-- Prove2me | Theorems.Thm_Formalism_L2_G_Cmp_mem_ratDom
-- name    : Formalism.L2.G.Cmp.mem_ratDom
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T07:54:23.8488+00:00
-- url     : https://prove2.me/theorems/b10fa147-c192-4775-87b0-d30cbe1fa0e3
-- title:
--   Cmp: mem rat Dom
-- statement:
--   The Cmp construction uses the mem rat Dom property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/GroupLattices/ComparisonMaps/IsComplRatCompl.lean#L153-L154
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/GroupLattices/ComparisonMaps/IsComplRatCompl.lean#L153-L154

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
variable {Cc : Type*} [Field Cc] {s : LL →+* Cc} {M0 M1 : Type*} [AddCommGroup M0] [Module Cc M0]
  [AddCommGroup M1] [Module Cc M1]

theorem Formalism.L2.G.Cmp.mem_ratDom (e0 : V0 →ₛₗ[s] M0) (e1 : V1 →ₛₗ[s] M1) (f : M0 →ₗ[Cc] M1) (x : V0) :
    x ∈ ratDom e0 e1 f ↔ ∃ y, e1 y = f (e0 x) := by sorry
