-- Prove2me | Theorems.Thm_Formalism_L2_G_Cmp_li_basis
-- name    : Formalism.L2.G.Cmp.li_basis
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T07:50:53.593462+00:00
-- url     : https://prove2.me/theorems/b751e3c7-a6c0-4831-8fc3-9f45fc52a4e7
-- title:
--   Cmp: li basis
-- statement:
--   The Cmp construction uses the li basis property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/GroupLattices/ComparisonMaps/IsComplRatCompl.lean#L126-L129
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/GroupLattices/ComparisonMaps/IsComplRatCompl.lean#L126-L129

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
open TensorProduct
variable {ι' : Type*}

theorem Formalism.L2.G.Cmp.li_basis (c0 : V0 →ₛₗ[e] W0) (b : Module.Basis ι LL V0)
    (hli : LinearIndependent Kf fun i => c0 (b i)) (b' : Module.Basis ι' LL V0) :
    LinearIndependent Kf fun i => c0 (b' i) := by sorry
