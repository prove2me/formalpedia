-- Prove2me | Theorems.Thm_Formalism_L2_Pj_LocFrM_range_free
-- name    : Formalism.L2.Pj.LocFrM.range_free
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T08:38:14.176462+00:00
-- url     : https://prove2.me/theorems/46366a58-fa7a-4995-84ad-3fd1aa5edd9d
-- title:
--   Loc Fr M: range free
-- statement:
--   The Loc Fr M construction uses the range free property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/ProjectiveLattices/GenSpecLocFrM.lean#L21-L24
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/ProjectiveLattices/GenSpecLocFrM.lean#L21-L24

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_GenSpecLocFrM
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism Formalism.L2 Formalism.L2.Pj Formalism.L2.Pj.LocFrM
open TensorProduct
variable {O : Type*} [CommRing O] [IsLocalRing O] {V : Type*} [AddCommGroup V] [Module O V]
  [Module.Free O V] [Module.Finite O V]

theorem Formalism.L2.Pj.LocFrM.range_free (e : Module.End O V) (he : IsIdempotentElem e) : Module.Free O (LinearMap.range e) := by sorry
