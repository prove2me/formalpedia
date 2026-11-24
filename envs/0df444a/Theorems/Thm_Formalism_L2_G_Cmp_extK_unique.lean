-- Prove2me | Theorems.Thm_Formalism_L2_G_Cmp_extK_unique
-- name    : Formalism.L2.G.Cmp.extK_unique
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T04:12:03.009153+00:00
-- url     : https://prove2.me/theorems/095b3929-1355-4659-bd1b-d56c0eb5930f
-- title:
--   Cmp: ext K unique
-- statement:
--   The Cmp construction uses the ext K unique property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/GroupLattices/ComparisonMaps/IsComplRatCompl.lean#L80-L90
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/GroupLattices/ComparisonMaps/IsComplRatCompl.lean#L80-L90

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

theorem Formalism.L2.G.Cmp.extK_unique (c0 : V0 →ₛₗ[e] W0) (c1 : V1 →ₛₗ[e] W1) (b : Module.Basis ι LL V0)
    (hli : LinearIndependent Kf fun i => c0 (b i)) (KL : V0 →ₗ[LL] V1) (g : W0 →ₗ[Kf] W1)
    (hg : ∀ x, g (c0 x) = c1 (KL x)) (y : W0) (hy : y ∈ spanK c0) : g y = extK c0 c1 b hli KL y := by sorry
