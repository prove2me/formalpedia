-- Prove2me | Theorems.Thm_Formalism_L2_G_Cmp_extK_apply
-- name    : Formalism.L2.G.Cmp.extK_apply
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T04:09:26.408475+00:00
-- url     : https://prove2.me/theorems/bf2638bf-69bf-45bd-afe3-67deee0062a5
-- title:
--   Cmp: ext K apply
-- statement:
--   The Cmp construction uses the ext K apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/GroupLattices/ComparisonMaps/IsComplRatCompl.lean#L72-L78
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/GroupLattices/ComparisonMaps/IsComplRatCompl.lean#L72-L78

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

theorem Formalism.L2.G.Cmp.extK_apply (c0 : V0 →ₛₗ[e] W0) (c1 : V1 →ₛₗ[e] W1) (b : Module.Basis ι LL V0)
    (hli : LinearIndependent Kf fun i => c0 (b i)) (KL : V0 →ₗ[LL] V1) (x : V0) :
    extK c0 c1 b hli KL (c0 x) = c1 (KL x) := by sorry
