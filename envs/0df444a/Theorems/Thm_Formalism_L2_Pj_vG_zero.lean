-- Prove2me | Theorems.Thm_Formalism_L2_Pj_vG_zero
-- name    : Formalism.L2.Pj.vG_zero
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T04:16:08.045944+00:00
-- url     : https://prove2.me/theorems/9be3fc95-2b2b-493f-adda-64fe18af4435
-- title:
--   Pj: v G zero
-- statement:
--   The Pj construction uses the v G zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/ProjectiveLattices/ErealAddIInf.lean#L58-L58
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/ProjectiveLattices/ErealAddIInf.lean#L58-L58

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

theorem Formalism.L2.Pj.vG_zero (h0 : v 0 = ⊤) : vG v (0 : AddMonoidAlgebra R M) = ⊤ := by sorry
