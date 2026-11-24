-- Prove2me | Theorems.Thm_Formalism_L2_Pj_LocFrM_range_projective
-- name    : Formalism.L2.Pj.LocFrM.range_projective
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T08:38:08.280618+00:00
-- url     : https://prove2.me/theorems/d745a182-ab43-46ab-83ab-92ea6e24e591
-- title:
--   Loc Fr M: range projective
-- statement:
--   The Loc Fr M construction uses the range projective property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/ProjectiveLattices/GenSpecLocFrM.lean#L12-L19
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/ProjectiveLattices/GenSpecLocFrM.lean#L12-L19

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

theorem Formalism.L2.Pj.LocFrM.range_projective (e : Module.End O V) (he : IsIdempotentElem e) :
    Module.Projective O (LinearMap.range e) := by sorry
