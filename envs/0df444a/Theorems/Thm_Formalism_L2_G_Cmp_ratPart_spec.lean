-- Prove2me | Theorems.Thm_Formalism_L2_G_Cmp_ratPart_spec
-- name    : Formalism.L2.G.Cmp.ratPart_spec
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T07:54:10.482802+00:00
-- url     : https://prove2.me/theorems/635e9c84-28fc-49c5-b1b7-25ae430b4a30
-- title:
--   Cmp: rat Part spec
-- statement:
--   The Cmp construction uses the rat Part spec property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/GroupLattices/ComparisonMaps/IsComplRatCompl.lean#L168-L169
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/GroupLattices/ComparisonMaps/IsComplRatCompl.lean#L168-L169

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

theorem Formalism.L2.G.Cmp.ratPart_spec (e0 : V0 →ₛₗ[s] M0) (e1 : V1 →ₛₗ[s] M1) (hinj : Function.Injective e1) (f : M0 →ₗ[Cc] M1)
    (x : ratDom e0 e1 f) : e1 (ratPart e0 e1 hinj f x) = f (e0 x) := by sorry
