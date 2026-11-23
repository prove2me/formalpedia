-- Prove2me | Theorems.Thm_Formalism_L2_Pj_vG_ne_bot
-- name    : Formalism.L2.Pj.vG_ne_bot
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T04:16:21.16497+00:00
-- url     : https://prove2.me/theorems/ec1f5e91-39a1-4dee-97b5-31eb341e4920
-- title:
--   Pj: v G ne bot
-- statement:
--   The Pj construction uses the v G ne bot property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/ProjectiveLattices/ErealAddIInf.lean#L108-L119
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/ProjectiveLattices/ErealAddIInf.lean#L108-L119

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_ErealAddIInf
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism Formalism.L2 Formalism.L2.Pj
variable {K R M W : Type} [Field K] [CommRing R] [Algebra K R] [AddCommMonoid M] (key : W → M)
  (C : W → Submodule K R)
variable {v : R → EReal}

theorem Formalism.L2.Pj.vG_ne_bot (h0 : v 0 = ⊤) (hb : ∀ r, v r ≠ ⊥) (x : AddMonoidAlgebra R M) : vG v x ≠ ⊥ := by sorry
