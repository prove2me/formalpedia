-- Prove2me | Theorems.Thm_Formalism_L2_Pj_vG_mul
-- name    : Formalism.L2.Pj.vG_mul
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T04:16:10.86173+00:00
-- url     : https://prove2.me/theorems/3efd9fa8-d701-4976-8bfe-a8da27f9f9ca
-- title:
--   Pj: v G mul
-- statement:
--   The Pj construction uses the v G mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/ProjectiveLattices/ErealAddIInf.lean#L121-L123
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/ProjectiveLattices/ErealAddIInf.lean#L121-L123

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

theorem Formalism.L2.Pj.vG_mul (h0 : v 0 = ⊤) (hm : ∀ r s, v (r * s) = v r + v s) (w w' : W) (F : C w) (F' : C w') :
    vG v (incG key C w F * incG key C w' F') = vG v (incG key C w F) + vG v (incG key C w' F') := by sorry
